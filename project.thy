theory project
imports Main
begin

axiomatization A :: "bool"
axiomatization B :: "bool"
axiomatization C :: "bool"
axiomatization D :: "bool"
axiomatization E :: "bool"
axiomatization F :: "bool"

axiomatization P :: "nat \<Rightarrow> bool"
axiomatization Q :: "nat \<Rightarrow> nat \<Rightarrow> bool"
axiomatization R :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
axiomatization f :: "nat \<Rightarrow> nat"
axiomatization a :: nat (*These are called arguments*)
axiomatization b :: nat (*These are called arguments*)


ML \<open>
(*MISCELLANEOUS FUNCTIONS AND VALUES*)

fun pwriteln t = Pretty.writeln t

fun pretty_term ctxt trm = Syntax.pretty_term ctxt trm

fun pretty_terms ctxt trms = Pretty.block (Pretty.commas (map (pretty_term ctxt) trms))

fun pretty_disj ctxt trms = Pretty.block (Pretty.separate " \<or>" (map (pretty_term ctxt) trms))

fun print_disj [] = writeln "False"
  | print_disj trm = pretty_disj @{context} trm |> Pretty.writeln

fun print_output (h::hs) = (print_disj h; print_output(hs))
  | print_output [] = writeln ""

fun contains(x, y::ys) = if x = y then true else contains(x, ys)
  | contains(_, []) = false

fun Not (Const ("HOL.Not", @{typ "bool \<Rightarrow> bool"}) $ a:term) = a (*Function to flip terms*)
  | Not a:term = Const ("HOL.Not", @{typ "bool \<Rightarrow> bool"}) $ a

val A = Logic.varify_global @{term A}
val B = Logic.varify_global @{term B}
val C = Logic.varify_global @{term C}
val D = Logic.varify_global @{term D}
val E = Logic.varify_global @{term E}
val F = Logic.varify_global @{term F}

val px = Logic.varify_global @{term "P x"}
val py = Logic.varify_global @{term "P y"}
val pz = Logic.varify_global @{term "P z"}
val pa = Logic.varify_global @{term "P a"}
val pb = Logic.varify_global @{term "P b"}
val pfx = Logic.varify_global @{term "P (f x)"}
val pfy = Logic.varify_global @{term "P (f y)"}
val pfa = Logic.varify_global @{term "P (f a)"}
val pfb = Logic.varify_global @{term "P (f b)"}
val qaa = Logic.varify_global @{term "Q a a"}
val qab = Logic.varify_global @{term "Q a b"}
val qba = Logic.varify_global @{term "Q b a"}
val qax = Logic.varify_global @{term "Q a x"}
val qxa = Logic.varify_global @{term "Q x a"}
val qxy = Logic.varify_global @{term "Q x y"}
val qxx = Logic.varify_global @{term "Q x x"}
val qyx = Logic.varify_global @{term "Q y x"}
val qfby = Logic.varify_global @{term "Q (f b) y"}
val qafx = Logic.varify_global @{term "Q a (f x)"}
val qbfx = Logic.varify_global @{term "Q b (f x)"}
val rabab = Logic.varify_global @{term "R a b a b"}
val rabaa = Logic.varify_global @{term "R a b a a"}
val gx = Logic.varify_global @{term "R a b a (f a)"}
\<close>

ML \<open>
(*SORTING AND ORDERING FUNCTIONS FOL*)
fun is_neg term = case term of
      Const (a, _) $ _ => if a = "HOL.Not" then true
                          else false
    | _ => false

fun get_head_name term = case head_of term of
      Const (a, _) => a
      | Var ((a, 0), _) => a
      | _ => error "Name not found"

(*Function to compare terms for sorting. Return 0 means term1 = term2, 1 means term1 < term2 and 
2 means term1 > term2.*)
fun sort_order term1 term2 =
      if term1 = term2 then 0 else
      (*1. Check the sign of the terms*)
      if is_neg term1 <>  is_neg term2 
      then if is_neg term1 then 1 else 2
      else 
        let
          val args1 = Term.args_of term1
          val args2 = Term.args_of term2
          val n_args1 = length args1
          val n_args2 = length args2
        in
          (*2. Check the number of arguments of the terms*)
          if n_args1 <> n_args2 
          then if n_args1 < n_args2 then 1 else 2
          else
            let
              val size1 = size_of_term term1
              val size2 = size_of_term term2
            in
              (*3. Check the overall size of the terms*)
              if size1 <> size2
              then if size1 < size2 then 1 else 2
              else
                let
                  val name1 = get_head_name term1
                  val name2 = get_head_name term2
                in
                  (*4. Check the name of the terms*)
                  if name1 <> name2 
                  then if name1 < name2 then 1 else 2
                  else
                    let
                      fun check_args (x::xs, y::ys) =
                            (case sort_order x y of
                              0 => check_args(xs, ys)
                              | 1 => 1
                              | 2 => 2
                              | _ => error "sort error 1")
                        | check_args (_, _) = error "sort error 2"
                    in
                      (*5. Check argument by argument until a difference is found*)
                      check_args(args1, args2)
                    end
                end
            end
        end;

(*compare == \<le>*)
fun compare term1 term2 = case sort_order term1 term2 of
      0 => true
      | 1 => true
      | 2 => false
      | _ => error "sort error 3";

fun ins_sort (x, []) = [x]
  | ins_sort (x, y::ys) = 
      if compare x y then x::y::ys
      else y::ins_sort(x, ys)

fun sort [] = []
  | sort (x::xs) = ins_sort(x, sort xs);

let
val input = [qaa, Not C, B, pa, Not B, D, gx, pfb, C, Not pfx, A, Not qxy, qafx, qba, Not qyx, Not D, D, Not A, A, rabaa, Not C]
in
sort input |> pretty_terms @{context}
end
\<close>


ML \<open>
(*FUNCTIONS FOR ELIMINATING DUPLICATE LITERALS*)

(*function that eliminates duplicate elements (literals) from a list (list needs to be sorted)*)
fun elim_dup (c::cs, output) = 
      if contains(c, output) then elim_dup (cs, output)
      else elim_dup (cs, output @ [c])
  | elim_dup ([], output) = output;

fun format_clause c = elim_dup(sort c, []);

let
val input = [qaa, Not C, B, pa, Not B, D, gx, pfb, C, Not pfx,
A, Not qxy, Not qyx, Not D, D, Not A, A, rabaa, Not C, pfa, Not qaa, pfb]
in
format_clause input |> pretty_terms @{context}
end;
\<close>

ML \<open>
(*COMBINATION FUNCTIONS*)
fun explode_list (l::ls) = [l]::explode_list(ls)
  | explode_list [] = nil;

fun combinations_r (c::cs, r) =
      if length (c::cs) < r then []
      else if r = 1 then explode_list(c::cs)
      else map (fn x => c::x) (combinations_r(cs, r-1)) @ combinations_r (cs, r)
  | combinations_r ([], _) = error "empty input reached";

fun all_combinations (c::cs) =
      let
        val l = length (c::cs)
        fun all_comb (c::cs, r, output) = 
              if r <= 0 then output
              else output @ combinations_r (c::cs, r) @ all_comb(c::cs, r-1, [])
          | all_comb (_, _, _) = error "combination error"
      in
        all_comb (c::cs, l, [])
      end
  | all_combinations [] = [];

fun zip (x::xs, y::ys) = (x, y) :: zip(xs, ys)
  | zip _ = [];

(*Function that inputs a clause and returns a tuple with the partition for the ordered resolution
of C v A_1 ... A_k, with the element in #1 are part of C and #2 corresponds to A_1 ... A_k.*)
fun unif_partition (c) =
      let
        val part = (all_combinations c) @ [[]]
      in
        zip(part, rev part) |> tl
      end
      

val lista = [A, B, C, D, pa];
(*unif_partition lista |> map (fn x => (#1 x |> print_disj; #2 x |> print_disj; writeln " "))*)
size_of_term (qaa)

\<close>

ML \<open>
(*UNIFICATION AND ORDERED RESOLUTION FUNCTIONS*)

(*Function that checks is an atom is maximal in a clause*)
fun is_max(x, c::cs) =
    let
    val c_ = (fn x => if is_neg x then Not x else x) c
    val x_ = (fn x => if is_neg x then Not x else x) c
    in
    if compare c_ x_ then is_max(x, cs)
    else false
    end
  | is_max(_, []) = true;


fun unify term1 term2 envir =
    let
      val unif = (Pattern.unify (Context.Proof @{context}) (term1, term2) envir) 
                  handle Pattern.Unif => Envir.empty 0
    in
      case Envir.maxidx_of unif of
        0 => (false, unif)
        | _ => (true, unif)
    end;

fun unify_terms (c::cs, t, output) =
      if (#1 output) then unify_terms (cs, t, unify c t (#2 output))
      else output
  | unify_terms ([], _, output) = output

fun subst env term = Envir.subst_term (Envir.type_env env, Envir.term_env env) term

fun subst_terms e c = map (subst e) c

(*Function that determines which literals from a clause are not individually unifiable with t in
from the ordered resolution. Returns a tuple. #1 is are the literals in k that are not
unifiable and #2 are the literals in k that are individually unifiable with t.*)
fun div_clause [] _ = error "error: div_clause an empty clause"
  | div_clause k t =
      let
        val unif_list = map (fn x => unify x t Envir.init) (k)
        fun divide (x::xs, y::ys, c, a) =
            if (#1 y) then divide (xs, ys, c, a @ [x])
            else divide (xs, ys, c @ [x], a)
          | divide ([], _, c, a) = (c, a)
          | divide (_, _, _, _) = error "error: divide (div_clause)"
      in
        divide (k, unif_list, [], [])
      end

(*Function that makes partition for all the unifiable possibilities of C v A_1 ... A_k. 
Returns a list of tuples with #1 being the C and #2 is the environment.*)
fun partition k t =
      let
        val (c, a) = div_clause k t
      in
        if a = nil then [(c, Envir.init)]
        else
        let
          (*og c-a partitions*)
          
          (*all possible c-a partitions*)
          val part = unif_partition a |> map (fn (x, y) => (x @ c, y))
          (*getting the environments*)
          val part_unif = map (fn (x, y) => (x, y, unify_terms(y, t, (true, Envir.init)))) part
          (*filtering the non-unifiable c-a partitions*)
          val part_fil = part_unif |> filter (fn (_, _, (x, _)) => x)
        in
          part_fil |> map (fn (x, _, (_, e)) => (format_clause x, e)) 
          |> filter (fn (x, _) => is_max(t, x))
        end
      end

fun resolution (l, t, d) =
      let
        val partitions = partition l t
      in
        map (fn (c, e) => (subst_terms e c) @ (subst_terms e d)) partitions
      end

fun order_res (l, r::rs, d, output) = 
      if not (is_max(r, (r::rs))) then order_res(l, rs, d @ [r], output)
      else if is_neg r then order_res (l, rs, d @ [r], output @ resolution (l, Not r, d @ rs))
      else output
  | order_res (_, [], _, output) = map format_clause output

(*Callable function for Ordered Resolution*)
fun ordered_res l r = order_res (l, r, [], []);

let
val left1 = [pz, A, pa, Not pb, B, qaa, pfa]
val right1 = [Not pa]
val left2 = [Not py, pa, px, pb, Not A, qxx, qxy]
val right2 = [Not px, Not qax, B]
val left3 = [A, A, B]
val right3 = [Not A, Not B]
in
ordered_res left3 right3 |> print_output
end
\<close>


ML \<open>
(*BINARY RESOLUTION WITH FACTORING FUNCTIONS*)

fun get_neg (a, b::ms, output) =
      if is_neg b then
        if a = Not b then (Not a)::output @ ms
        else get_neg (a, ms, output @ [b])
      else get_neg (a, ms, output @ [b])
  | get_neg (_, [], _) = error "No negative occurrence of 'a' was found"

fun inf_exec (l::ls, r::rs, output, result) =
      if is_neg r then
        if l = Not r then inf_exec (ls, r::rs, output, (output @ ls @ rs)::result)
        else inf_exec (ls, r::rs, l::output, result)
      else error "Secondary premise does not start with a negative occurrence of 'a'"
  | inf_exec ([], _, _, result) = result
  | inf_exec (_ , _, _, _) = 
      error "inf_exec error"

fun brf (l, r, a::rs, history, output) =
      if is_neg a then
        if not (contains(Not a, history))
        then brf (l, r, rs, (Not a)::history, (inf_exec(l, get_neg(Not a, r, []), [], [])) @ output)
        else brf (l, r, rs, history, output)
      else brf (l, r, rs, history, output)
  | brf (_, _, [], _, output) = output;

(*Binary Resolution with Factoring callable function*)
fun bin_res_fac l r = map format_clause (brf(l, r, r, [], []));

let
(*comment like this*)
(*Testing...*)
val left = [Not A, Not C, A, B, D]
val right = [Not B, Not D, F]
in
writeln "OUTPUT:";
bin_res_fac left right |> print_output
end
\<close>

ML \<open>
(*FUNCTIONS FOR TAUTOLOGY AND SUBSUMPTION REDUNDANCY CHECKS*)

(*Function that checks if clause is a tautology. Only checks for complementary cases of tautology.
Assumes clause is sorted.*)
fun is_tau (x::xs) = 
      if contains (Not x, xs) then true
      else is_tau (xs)
  | is_tau [] = false

(*Tautology deletion*)
fun tau_del (x::xs, output) = 
      if is_tau x then tau_del(xs, output)
      else tau_del (xs, output @ [x])
  | tau_del ([], output) = output
fun tautology_del x = tau_del(x, []) (*call this one*)

(*Function that checks for non-strict subsumption (\<ge>). Assumes that duplicate literals have been
removed. For subsums(p, p\<or>q) = true*)
fun subsums_ns ((x:term)::xs, y) =
      if contains(x, y) then subsums_ns(xs, y)
      else false
  | subsums_ns ([], _) = true
(*Function that checks for strict subsumption (>). Assumes that duplicate literals have been
removed. For subsums(p, p\<or>q) = true*)
fun subsums_st (x::xs, y) = 
      if x::xs = y then false
      else subsums_ns (x::xs, y)
  | subsums_st([], _) = true
(*Function that checks if x is subsumed by one of the clauses in y::ys*)
fun subsums_ns_check (x, y::ys) = 
      if subsums_ns(y, x) then true
      else subsums_ns_check(x, ys)
  | subsums_ns_check (_, []) = false
(*Function that checks if x is properly subsumed by one of the clauses in y::ys*)
fun subsums_st_check (x, y::ys) = 
      if subsums_st(y, x) then true
      else subsums_st_check(x, ys)
  | subsums_st_check (_, []) = false

(*Function that eliminates redundancy via non-strict subsumption on a set of clauses based on 
the clauses of another set of clauses.*)
fun f_sub_active (p::ps, a, output) =
      if subsums_ns_check (p, a) then f_sub_active (ps, a, output)
      else f_sub_active (ps, a, output @ [p])
  | f_sub_active ([], _, output) = output

fun f_sub_passive (p::ps,output) =
      if subsums_ns_check (p, ps @ output) then f_sub_passive (ps, output)
      else f_sub_passive (ps, output @ [p])
  | f_sub_passive ([], output) = output

(*Function that eliminates redundancy via strict subsumption on a set of clauses based on 
the clauses of another set of clauses.*)
fun b_sub (a::ax, p, output) = 
      if subsums_st_check (a, p) then b_sub (ax, p, output)
      else b_sub (ax, p, output @ [a])
  | b_sub ([], _, output) = output

(*Subsumption rules: a and p are sets of clauses*)
fun forward_sub_active a p = f_sub_active(p, a, []) (*a is the active set and p is the passive set*)
fun forward_sub_passive p = f_sub_passive(p, []) (*p is the passive set*)
fun forward_sub a p = forward_sub_passive p |> forward_sub_active a
fun backward_sub p a = b_sub(a, p, []);

let
val passive = [[]]
val active = [[A], [Not A]]
val t = [[], [D], [Not A, A], [Not B, C]]
in
writeln "Forward active:";
forward_sub_active active passive |> print_output;
writeln "Forward passive:";
forward_sub_passive passive |> print_output;
writeln "Forward:";
forward_sub active passive |> print_output;
writeln "Backward:";
backward_sub passive active |> print_output;
writeln "Tautology:";
tautology_del t |> print_output
end
\<close>


ML\<open>
(*FUNCTIONS FOR REDUCTION REDUNDANCY CHECKS*)

(*Function for reduction. x is the C v L clause and y::ys is the D v L' clause.*)
fun reduction (x, y::ys, z) = 
      if not (is_neg y) then reduction (x, ys, z @ [y])
      else
        let
          val x_fil = filter (fn a => a <> Not y) x
        in
          if contains(Not y, x) andalso subsums_ns(z @ ys, x_fil) then x_fil
          else reduction (x, ys, z @ [y])
        end
  | reduction (x, [], _) = x;

(*Function that applies reduction to a clause from a set of clauses.*)
fun reduc_check (c, s::ss) = reduc_check(reduction(c, s, []), ss)
  | reduc_check (c, []) = c

fun f_reduc_passive p = map (fn x => reduc_check(x, p)) p

fun f_reduc_active a p = map (fn x => reduc_check(x, a)) p

(*Function that does forward reduction*)
fun forward_reduc a p = p |> f_reduc_passive |> f_reduc_active a

(*Function that does backward reduction. a::ax and p are the input active and passive sets
respectively. x are the clauses that will stay in the active set as C v L, and y are the clauses that will
move to the passive set as C.*)
fun b_reduc (a::ax, p, x, y) = 
      let
        val a_red = reduc_check(a, p)
      in
        if a = a_red then b_reduc(ax, p, x @ [a], y)
        else b_reduc(ax, p, x, y @ [a_red])
      end
  | b_reduc ([], p, x, y) = (p @ y, x)

(*Function for backward reduction. Pretty callable version.*)
fun backward_reduc p a = b_reduc(a, p, [], []);

let
val passive = [[Not A]]
val active = [[A]]
in
backward_reduc passive active |> #1 |> print_output
end
\<close>


ML\<open>
(*FUNCTIONS FOR GIVEN CLAUSE ALGORITHM*)

(*function that gets the first smallest clause from a list and also returns the rest of the list*)
fun get_smallest(c::(s::cs), t) = 
      if length c > length s then get_smallest(s::cs, c::t)
      else get_smallest(c::cs, s::t)
  | get_smallest(c::[], t) = (c, t)
  | get_smallest(_, _) = error "error"
(*function that chooses the next clause*)
fun choose(c::cs, n) = 
      if (n mod 10 = 0) then (c, cs)
      else get_smallest(c::cs, [])
  | choose ([], _) = error "passive set is empty"
(*function that executes the binary resolution with factoring to the active set*)
fun brf_exec(c, a::ac) = bin_res_fac a c @ bin_res_fac c a @ brf_exec(c, ac)
  | brf_exec(_, []) = [] 
(*funtion that executes the ordered resolution to the active set*)
fun ord_exec(c, a::ac) = ordered_res a c @ ordered_res c a @ ord_exec(c, ac)
  | ord_exec(_, []) = []
(*given clause algorithm function*)
fun gca([], _, _) = false
  | gca(p, a, n) = 
      if n > 0 then
      if contains([], p) then true
      else 
        let
          val (c, rest) = choose(map format_clause p |> tautology_del, n)
          val active_ = c::a
          val passive_ = rest @ ord_exec(c, active_) |> tautology_del
          val passive_sub = passive_ |> forward_sub active_
          val active_sub = active_ |> backward_sub passive_sub
          val passive_reduc = passive_sub |> forward_reduc active_sub
          val (passive, active) = backward_reduc passive_reduc active_sub
        in
          (*writeln (@{make_string} n);
          writeln "PASSIVE";
          passive |> print_output;
          writeln "ACTIVE";
          active |> print_output;*)
          gca(passive, active, n-1)
        end
      else error "Not enough iterations to process the result"

fun logic_prover input n = gca(input, [], n)

fun logic_prover_pretty input n = 
    if logic_prover input n then writeln "A contradiction was found in n iterations!"
    else writeln "A contradiction was NOT found the n iterations";

let
val input1 = [[Not A, B], [Not B, C], [A, Not C], [A, B, C], [Not A, Not B, Not C]]
val input2 = [[Not A], [A]]
val input3 = [[Not px], [pa, pz, py]]
val input4 = [[Not qax], [px, qab], [Not pa]]
val input5 = [[Not A, B], [Not B, C], [A, C], [A, B, C], [Not A, Not B, Not C], [pfa], [Not px]]
val input6 = [[Not A, C], [Not B, D], [A, B, C, D], [Not C, B, D], [Not D]]
in
logic_prover_pretty input1 10;
logic_prover_pretty input2 10;
logic_prover_pretty input3 10;
logic_prover_pretty input4 10;
logic_prover_pretty input5 10;
logic_prover_pretty input6 10
end
\<close>


