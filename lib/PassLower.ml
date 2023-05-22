open Lir
open Printf

(* Here we just show it works, emitted code is terrible:
 *
 * assumes all values are 64-bits
 * rsp and rbp business as usual (may omit rbp)
 * for internal calls, the stack looks like this:
 *
 * | free space  |
 * | return addr | <- rsp
 * |   arg 5     | <- rsp+8
 * |   arg 6     |
 * |   arg 7+    |
 *
 * args 1, 2, 3, 4 are passed via rdi, rsi, rcx, rdx
 * return value goes into rax and edx (see below)
 * these registers are caller-saved
 * caller cleans up the arguments
 *
 * in our simplified model, a non-zero edx indicates an exception has
 * happened. in this case, rax holds the value thrown. the caller looks at rdx
 * after each call and decides if unwinding is needed.
 *
 * foreign calls clearly have to comply with whatever calling convention they
 * use.
 *
 * we synthesize a main function which calls the module initializer.
 * link with a gc library (expects GC_init and GC_malloc symbols).
 *)

let rec map_module_value : value -> unit = function
  | Local _ -> failwith "Module level value cannot reference a local value"
  | Label _ -> failwith "Cannot map a label without a Globl name"
  | Globl n ->
    printf "    .quad _module_%s\n" n
  | Int64 v ->
    printf "    .quad %Lu\n" v
  | Flt64 v ->
    printf "    .quad 0x%Lx   # double %e\n" (Int64.bits_of_float v) v
  | Tuple xs ->
    List.iter map_module_value xs

let alloc_locals ((args, _, blocks) : label) =
  (* do the dumbest thing, which is to allocate everything onto the stack even
   * if it is not simultaneously live. *)

  (* by SSA rules, any name is only assigned once, hence this scheme is dumb,
   * but notice that the incoming arguments are also never modified. that
   * means we conservatively move args 1 to 4 onto the stack, the rest just
   * fetch from the stack directly! *)
  let rec collect_regargs idx offs acc = function
    | xs when idx = 0 -> (acc, offs, xs)
    | [] -> (acc, offs, [])
    | x :: xs ->
      collect_regargs (idx - 1) (offs - 8) (M.add x offs acc) xs in

  let rec collect_stackargs offs acc = function
    | [] -> (acc, offs)
    | x :: xs ->
      collect_stackargs (offs + 8) (M.add x offs acc) xs in

  let collect_locals offs acc blocks =
    M.fold (fun _ (args, instrs, _) acc ->
      let acc = List.fold_left (fun (acc, offs) arg ->
        (M.add arg offs acc, offs - 8)) acc args in
      let acc = List.fold_left (fun (acc, offs) -> function
        | ICall (n, _, _) | IOffs (n, _, _) | IPack (n, _) | ILoad (n, _) ->
          (M.add n offs acc, offs - 8)
        | IStore _ -> (acc, offs)) acc instrs in
      acc) blocks (acc, offs) in

  (* offsets assume rbp relative indices (of course rbp saved) *)
  let (m, offs, xs) = collect_regargs 4 (-8) M.empty args in
  let (m, _) = collect_stackargs 16 m xs in
  let (m, offs) = collect_locals offs m blocks in
  (m, -(offs + 8))

let map_module_label prefix (((args, entry, blocks) as lbl) : label) =
  let (m, maxstack) = alloc_locals lbl in

  let rec map_regargs names slots = match names, slots with
    | arg :: xs, reg :: ys ->
      printf "    movq %s, %d(%%rbp)  # $%s\n" reg (M.find arg m) arg;
      map_regargs xs ys
    | _ -> () in

  printf "    pushq %%rbp\n";
  printf "    movq %%rsp, %%rbp\n";
  printf "    subq $%d, %%rsp\n" maxstack;
  map_regargs args ["%rdi"; "%rsi"; "%rcx"; "%rdx"];

  let load_simple_value reg = function
    | Tuple [] -> ()
    | Local v ->
      printf "    movq %d(%%rbp), %s  # $%s\n" (M.find v m) reg v
    | Globl v ->
      printf "    leaq _module_%s(%%rip), %s\n" v reg
    | Int64 v ->
      printf "    movq $%Lu, %s\n" v reg
    | Flt64 v ->
      printf "    movq $0x%Lu, %s  # double %e\n" (Int64.bits_of_float v) reg v
    | _ -> failwith "VALUE IS NOT SIMPLE" in

  let map_block n ((_, instrs, tail) : block) =
    printf ".L%s_%s:\n" prefix n;

    let map_usual_call f args =
      let rec load_regargs names slots = match names, slots with
        | arg :: xs, reg :: ys ->
          load_simple_value reg arg;
          load_regargs xs ys
        | args, _ -> args in

      let stackargs = load_regargs args ["%rdi"; "%rsi"; "%rcx"; "%rdx"] in
      let () = stackargs
        |> List.rev
        |> List.iter (fun a ->
          load_simple_value "%rax" a;
          printf "    pushq %%rax\n") in
      let () = match f with
        | Globl f ->
          printf "    callq _module_%s\n" f;
        | _ ->
          load_simple_value "%rax" f;
          printf "    jmpq *%%rax\n" in

      (* call has returned, so cleanup the stack *)
      printf "    addq $%d, %%rsp\n" (8 * List.length stackargs) in

    List.iter (function
      | ICall (dst, f, args) ->
        map_usual_call f args;
        (* manually unwind on exception *)
        printf "    testl %%eax, %%eax\n";
        printf "    jz 0f\n";
        printf "    leaveq\n";
        printf "    retq\n";
        printf "0:  movq %%rax, %d(%%rbp)\n" (M.find dst m)

      | IOffs (dst, addr, offs) ->
        load_simple_value "%rax" addr;
        printf "    addq $%Lu, %%rax\n" (Int64.mul 8L offs);
        printf "    movq %%rax, %d(%%rbp)\n" (M.find dst m)

      | ILoad (dst, Globl sym) ->
        printf "    movq _module_%s(%%rip), %%rax\n" sym;
        printf "    movq %%rax, %d(%%rbp)\n" (M.find dst m)

      | ILoad (dst, addr) ->
        load_simple_value "%rax" addr;
        printf "    movq (%%rax), %%rax\n";
        printf "    movq %%rax, %d(%%rbp)\n" (M.find dst m)

      | IStore (v, Globl sym) ->
        load_simple_value "%rax" v;
        printf "    movq %%rax, _module_%s(%%rip)\n" sym

      | IStore (v, addr) ->
        load_simple_value "%rax" addr;
        load_simple_value "%rdi" v;
        printf "    movq %%rdi, (%%rax)\n"

      | IPack (dst, elts) ->
        printf "    movq $%d, %%rdi\n" (8 * List.length elts);
        printf "    callq _GC_malloc\n";
        List.iteri (fun i e ->
          load_simple_value "%rdx" e;
          printf "    movq %%rdx, %d(%%rax)\n" (8 * i)) elts;
        printf "    movq %%rax, %d(%%rbp)\n" (M.find dst m)) instrs;

    match tail with
      | KDead ->
        printf "    # (unreachable)\n"

      | KRetv v ->
        load_simple_value "%rax" v;
        printf "    xorl %%edx, %%edx\n";
        printf "    leaveq\n";
        printf "    retq\n"

      | KThrow v ->
        load_simple_value "%rax" v;
        printf "    movl $1, %%edx\n";
        printf "    leaveq\n";
        printf "    retq\n"

      | KCase (v, k, cases) ->
        (* keep it simple and emit linear search *)
        load_simple_value "%rax" v;
        List.iter (fun (v, k) ->
          printf "    cmpq $%Lu, %%rax\n" v;
          printf "    je .L%s_%s" prefix k) cases;
        printf "    jmp .L%s_%s\n" prefix k

      | KCatch (f, k, h, args) ->
        map_usual_call f args;

        (* jump to the corresponding contination depending on edx *)
        let (kparam, _, _) = M.find k blocks in
        let (hparam, _, _) = M.find h blocks in
        printf "    testq %%edx, %%edx\n";
        printf "    jnz 0f\n";
        printf "    movq %%rax, %d(%%rbp)\n" (M.find (List.hd kparam) m);
        printf "    jmp .L%s_%s\n" prefix k;
        printf "0:  movq %%rax, %d(%%rbp)\n" (M.find (List.hd hparam) m);
        printf "    jmp .L%s_%s\n" prefix h;

      | KJump (k, args) ->
        (* make a simplification and say that every local phi move might
         * overwrite the value (which is definitely not true) and use the
         * stack for those cases. *)
        let (params, _, _) = M.find k blocks in
        let easy, diff = List.fold_left2 (fun (easy, diff) p a ->
          match a, p with
            | Local a, b when a = b -> (easy, diff)
            | Local _, _ -> (easy, (p, a) :: diff)
            | _ -> ((p, a) :: easy, diff)) ([], []) params args in

        let diff = List.fold_left (fun diff (p, a) ->
          load_simple_value "%rax" a;
          printf "    pushq %%rax\n";
          p :: diff) [] diff in
        List.iter (fun p ->
          printf "    popq %%rax\n";
          printf "    movq %%rax, %d(%%rbp)\n" (M.find p m)) diff;
        List.iter (fun (p, a) ->
          load_simple_value "%rax" a;
          printf "    movq %%rax, %d(%%rbp)\n" (M.find p m)) easy;
        printf "    jmp .L%s_%s\n" prefix k

      | KCall (f, args) -> begin
        let try_pass_by_reg names slots =
          let rec loop acc names slots = match names, slots with
            | arg :: xs, reg :: ys ->
              loop ((reg, arg) :: acc) xs ys
            | [], _ -> Some acc
            | _ -> None in
          loop [] names slots in

        let () = match try_pass_by_reg args ["%rdi"; "%rsi"; "%rcx"; "%rdx"] with
          | Some acc ->
            List.iter (fun (r, a) -> load_simple_value r a) acc;
            printf "    leaveq\n"
          | None ->
            (* right now, our stack looks like this:
             *
             * | locals  |
             * | old rbp | <- reference point
             * | retaddr |
             *
             * we want to turn it into this:
             *
             * | retaddr |
             * | arg 5+  |
             * | arg n-1 | <- reference point (with rbp restored)
             * | arg n   |
             *)
            printf "    movq (%%rbp), %%rsi\n";   (* old rbp *)
            printf "    movq 8(%%rbp), %%rdi\n";  (* old return address *)

            let len = List.length args in

            (*
| arg 1   | <- rsp
| ...     |
| arg 4   |
| arg 5   | <- rsp + 8*4
| arg 6   | <- rsp + 8*5
| locals? |
| old rbp | <-
| retaddr |
             *)
            let () = args
              |> List.rev
              |> List.iter (fun a ->
                load_simple_value "%rax" a;
                printf "    pushq %%rax\n") in

            (*
| arg 1   | \
| ...     |  |
| arg 3   |  | this part is effectively garbage after this step
| arg 4   |  |
| locals? | /
| retaddr | <- rsp
| arg 5   | <-
| arg 6   |
            *)
            let rec loop len offs =
              if len = 4 then begin
                printf "    leaq %d(%%rbp), %%rax" offs;
                printf "    movq %%rdi, %d(%%rbp)\n" offs;
                printf "    movq %%rsi, %%rbp\n";
                printf "    movq (%%rsp), %%rdi\n";
                printf "    movq 8(%%rsp), %%rsi\n";
                printf "    movq 16(%%rsp), %%rcx\n";
                printf "    movq 24(%%rsp), %%rdx\n";
                printf "    movq %%rax, %%rsp\n";
              end else begin
                printf "    movq %d(%%rsp), %%rax\n" (8 * (len - 1));
                printf "    movq %%rax, %d(%%rbp)\n" offs;
                loop (len - 1) (offs - 8)
              end in
            loop len 8 in
        match f with
          | Globl f ->
            printf "    jmp _module_%s\n" f;
          | _ ->
            load_simple_value "%rax" f;
            printf "    jmpq *%%rax\n"
      end in

  let (m1, b1, m2) = M.split entry blocks in
  map_block entry (Option.get b1);
  M.iter map_block m1;
  M.iter map_block m2

let lower e =
  M.iter (fun n -> function
    | Label lbl ->
      printf "    .text\n";
      printf "    .global _module_%s\n" n;
      printf "_module_%s:\n" n;
      map_module_label n lbl
    | v ->
      printf "    .data\n";
      printf "    .global _module_%s\n" n;
      printf "_module_%s:\n" n;
      map_module_value v) e;

  printf "    .text\n";
  printf "    .globl _main\n";
  printf "_main:\n";
  printf "    pushq %%rbp\n";
  printf "    movq %%rsp, %%rbp\n";
  printf "    callq _GC_init\n";
  printf "    leaveq\n";
  printf "    jmp _module_INIT\n"
