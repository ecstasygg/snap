theory Frontend
  imports Machine "HOL-Library.Code_Target_Numeral"
begin

datatype 'a result = Error string | Ok 'a

fun bind :: "'a result \<Rightarrow> ('a \<Rightarrow> 'b result) \<Rightarrow> 'b result" where
  "bind (Error e) f = Error e"
| "bind (Ok x) f = f x"

function decimal :: "nat \<Rightarrow> string" where
  "decimal n = (if n < 10 then [char_of_nat (48 + n)] else decimal (n div 10) @ [char_of_nat (48 + n mod 10)])"
  by pat_completeness auto
termination by (relation "measure id") (auto simp: div_less_dividend)

definition newline :: string where "newline = [CHR 0x0A]"

fun separate :: "char \<Rightarrow> string \<Rightarrow> string list" where
  "separate c [] = [[]]"
| "separate c (x # xs) = (if x = c then [] # separate c xs else
    case separate c xs of [] \<Rightarrow> [[x]] | y # ys \<Rightarrow> (x # y) # ys)"

definition words :: "string \<Rightarrow> string list" where
  "words s = filter (\<lambda>x. x \<noteq> []) (separate CHR '' ''
    (map (\<lambda>c. if c = CHR 0x09 \<or> c = CHR 0x0D then CHR '' '' else c) s))"

definition number :: "string \<Rightarrow> nat option" where
  "number s = (if s \<noteq> [] \<and> list_all (\<lambda>c. 48 \<le> nat_of_char c \<and> nat_of_char c < 58) s then
    let n = foldl (\<lambda>n c. min 65537 (10 * n + nat_of_char c - 48)) 0 s in
    if n \<le> 65536 then Some n else None else None)"

datatype statement = Label string | Emit "string instruction" | Pad nat

definition parse_line :: "nat \<Rightarrow> string list \<Rightarrow> statement list result" where
  "parse_line n tokens = (let bad = Error (''invalid instruction at line '' @ decimal n) in
    case tokens of [] \<Rightarrow> Ok []
    | [a] \<Rightarrow> if a = ''nop'' then Ok [Emit Nop] else if a = ''inc'' then Ok [Emit Inc]
      else if a = ''dec'' then Ok [Emit Dec] else if a = ''halt'' then Ok [Emit Stop] else bad
    | [a,b] \<Rightarrow> if a = ''label'' then Ok [Label b] else if a = ''jmp'' then Ok [Emit (Jump b)]
      else if a = ''jz'' then Ok [Emit (Zero b)] else if a = ''pad'' then
        (case number b of None \<Rightarrow> Error (''invalid padding at line '' @ decimal n) | Some k \<Rightarrow> Ok [Pad k])
      else bad
    | _ \<Rightarrow> bad)"

fun parse_lines :: "nat \<Rightarrow> string list \<Rightarrow> statement list result" where
  "parse_lines n [] = Ok []"
| "parse_lines n (s # ss) = bind (parse_line n (words s)) (\<lambda>xs.
    bind (parse_lines (Suc n) ss) (\<lambda>ys. Ok (xs @ ys)))"

fun count :: "statement \<Rightarrow> nat" where
  "count (Label l) = 0"
| "count (Emit op) = 1"
| "count (Pad n) = n"

fun collect :: "statement list \<Rightarrow> nat \<Rightarrow> (string \<times> nat) list \<Rightarrow> (string \<times> nat) list result" where
  "collect [] pc env = Ok env"
| "collect (Label l # ss) pc env = (if map_of env l \<noteq> None then Error (''duplicate label '' @ l)
    else collect ss pc ((l,pc) # env))"
| "collect (s # ss) pc env = collect ss (pc + count s) env"

fun resolve :: "(string \<times> nat) list \<Rightarrow> string instruction \<Rightarrow> nat instruction result" where
  "resolve env Nop = Ok Nop"
| "resolve env Inc = Ok Inc"
| "resolve env Dec = Ok Dec"
| "resolve env Stop = Ok Stop"
| "resolve env (Jump l) = (case map_of env l of None \<Rightarrow> Error (''undefined label '' @ l) | Some t \<Rightarrow> Ok (Jump t))"
| "resolve env (Zero l) = (case map_of env l of None \<Rightarrow> Error (''undefined label '' @ l) | Some t \<Rightarrow> Ok (Zero t))"

fun resolve_all :: "(string \<times> nat) list \<Rightarrow> statement list \<Rightarrow> nat instruction list result" where
  "resolve_all env [] = Ok []"
| "resolve_all env (Label l # ss) = resolve_all env ss"
| "resolve_all env (Emit op # ss) = bind (resolve env op) (\<lambda>x.
    bind (resolve_all env ss) (\<lambda>xs. Ok (x # xs)))"
| "resolve_all env (Pad n # ss) = bind (resolve_all env ss) (\<lambda>xs. Ok (replicate n Nop @ xs))"

definition source :: "string \<Rightarrow> nat instruction list result" where
  "source s = (if \<not> list_all (\<lambda>c. let n = nat_of_char c in
      n = 9 \<or> n = 10 \<or> n = 13 \<or> (32 \<le> n \<and> n < 127)) s
    then Error ''source must contain printable ASCII, tabs, or line endings'' else
    bind (parse_lines 1 (separate CHR 0x0A s)) (\<lambda>ss.
    if sum_list (map count ss) > 65536 then Error ''program exceeds 65536 instructions''
    else bind (collect ss 0 []) (\<lambda>env. bind (resolve_all env ss) (\<lambda>p.
      if wellformed p then Ok p else Error ''branch targets a label after the final instruction''))))"

definition checked :: "nat instruction list \<Rightarrow> nat list result" where
  "checked p = (if \<not> wellformed p then Error ''invalid branch target'' else
    let W = layout p in if valid p W then Ok (bytecode p W)
    else Error ''branch displacement exceeds the signed 16-bit range'')"

lemma checked_assemble:
  "checked p = Ok code \<longleftrightarrow> assemble p = Some code"
  by (auto simp: checked_def assemble_def Let_def split: if_splits)

theorem checked_execution:
  "checked p = Ok code \<Longrightarrow>
    execute (machine_step code) fuel (0,a) = relocate p (layout p) (execute (source_step p) fuel (0,a))"
  by (simp add: checked_assemble assembly_execution)

function history :: "nat instruction list \<Rightarrow> nat set \<Rightarrow> nat set list" where
  "history p W = (if widen p W = W then [W] else W # history p (widen p W))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(p,W). card (branches p - W))") (auto intro: widen_decreases)

declare history.simps [simp del]

lemma history_nonempty: "history p W \<noteq> []"
  by (subst history.simps) auto

lemma history_last: "last (history p W) = settle p W"
  by (induction p W rule: history.induct)
    (subst history.simps, subst settle.simps, auto simp: history_nonempty)

definition hexbyte :: "nat \<Rightarrow> string" where
  "hexbyte n = [''0123456789abcdef'' ! (n div 16 mod 16), ''0123456789abcdef'' ! (n mod 16)]"

fun joined :: "string \<Rightarrow> string list \<Rightarrow> string" where
  "joined sep [] = []"
| "joined sep (x # xs) = x @ (if xs = [] then [] else sep @ joined sep xs)"

definition hex :: "nat list \<Rightarrow> string" where
  "hex bs = joined '' '' (map hexbyte bs)"

definition signed :: "int \<Rightarrow> string" where
  "signed n = (if n < 0 then ''-'' @ decimal (nat (-n)) else ''+'' @ decimal (nat n))"

fun opname :: "operation \<Rightarrow> string" where
  "opname Idle = ''nop''"
| "opname Raise = ''inc''"
| "opname Lower = ''dec''"
| "opname Finish = ''halt''"
| "opname (Branch c wide d) = (if c then ''jz.'' else ''jmp.'') @ (if wide then ''16 '' else ''8 '') @ signed d"

definition branchline :: "nat instruction list \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> string" where
  "branchline p W i = ''  #'' @ decimal i @ ''  @'' @ decimal (address p W i) @ ''  '' @
    opname (lower p W i (p ! i)) @ ''  -> @'' @ decimal (address p W (destination p i)) @ newline"

definition passline :: "nat instruction list \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> string" where
  "passline p n W = ''pass '' @ decimal n @ ''  '' @ decimal (address p W (length p)) @
    '' bytes  widen ['' @ joined '', '' (map decimal (filter (\<lambda>i. i \<in> pending p W) [0..<length p])) @ '']'' @ newline @
    concat (map (branchline p W) (filter (\<lambda>i. i \<in> branches p) [0..<length p]))"

definition trace :: "nat instruction list \<Rightarrow> string" where
  "trace p = (let hs = history p {} in concat (map (\<lambda>i. passline p i (hs ! i)) [0..<length hs]))"

definition summary :: "nat instruction list \<Rightarrow> nat list \<Rightarrow> string" where
  "summary p bs = decimal (length p) @ '' instructions, '' @ decimal (length bs) @ '' bytes, '' @
    decimal (card (layout p)) @ '' long branches'' @ newline"

definition compile :: "string \<Rightarrow> nat list result" where
  "compile s = bind (source s) checked"

theorem compile_sound:
  "compile s = Ok code \<Longrightarrow> \<exists>p. source s = Ok p \<and> assemble p = Some code"
  unfolding compile_def by (cases "source s") (auto simp: checked_assemble)

theorem checked_failure:
  "wellformed p \<Longrightarrow> checked p = Error e \<Longrightarrow> \<not> (\<exists>W. valid p W)"
  using assembly_complete[of p]
  by (auto simp: checked_def assemble_def split: if_splits)

definition stopped :: "nat list \<Rightarrow> nat \<times> nat \<Rightarrow> string" where
  "stopped bs s = (case map_option fst (decode (drop (fst s) bs)) of
    Some Finish \<Rightarrow> ''halted'' | _ \<Rightarrow> if machine_step bs s = None then ''fault'' else ''fuel exhausted'')"

definition runreport :: "nat list \<Rightarrow> nat \<Rightarrow> string" where
  "runreport bs fuel = (let s = execute (machine_step bs) fuel (0,0) in
    stopped bs s @ ''  pc='' @ decimal (fst s) @ ''  acc='' @ decimal (snd s) @ newline)"

function listing :: "nat \<Rightarrow> nat list \<Rightarrow> string result" where
  "listing pc bs = (if bs = [] then Ok [] else case decode bs of None \<Rightarrow> Error (''invalid encoding at byte '' @ decimal pc)
    | Some (op,rest) \<Rightarrow> if length rest < length bs then
      bind (listing (pc + bytesize op) rest) (\<lambda>s. Ok (decimal pc @ ''  '' @
        hex (take (bytesize op) bs) @ ''  '' @ opname op @ newline @ s)) else Error ''invalid decoder progress'')"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(pc,bs). length bs)") auto

definition binary :: "string \<Rightarrow> bool \<times> string" where
  "binary s = (case compile s of Error e \<Rightarrow> (False, e @ newline) | Ok bs \<Rightarrow> (True, map char_of_nat bs))"

definition disassemble :: "string \<Rightarrow> bool \<times> string" where
  "disassemble s = (case listing 0 (map nat_of_char s) of Error e \<Rightarrow> (False,e @ newline) | Ok text \<Rightarrow> (True,text))"

definition inspect :: "string list \<Rightarrow> nat instruction list \<Rightarrow> nat list \<Rightarrow> bool \<times> string" where
  "inspect args p bs = (let bad = (False, ''usage: span {assemble|trace|list|run} file [fuel]'' @ newline) in
    case args of [mode] \<Rightarrow>
      if mode = ''assemble'' then (True, summary p bs @ hex bs @ newline)
      else if mode = ''trace'' then (True, trace p @ summary p bs)
      else if mode = ''list'' then (case listing 0 bs of Error e \<Rightarrow> (False,e @ newline) | Ok s \<Rightarrow> (True,s))
      else bad
    | [mode,n] \<Rightarrow> if mode = ''run'' then
      (case number n of None \<Rightarrow> (False,''fuel must be between 0 and 65536'' @ newline)
       | Some fuel \<Rightarrow> (True, runreport bs fuel)) else bad
    | _ \<Rightarrow> bad)"

definition process :: "string list \<Rightarrow> string \<Rightarrow> bool \<times> string" where
  "process args s = (case source s of Error e \<Rightarrow> (False, e @ newline) | Ok p \<Rightarrow>
    case checked p of Error e \<Rightarrow> (False, (if args = [''trace''] then trace p else []) @ e @ newline)
    | Ok bs \<Rightarrow> inspect args p bs)"

end
