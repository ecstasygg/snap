theory Encoding
  imports Relax
begin

datatype operation = Idle | Raise | Lower | Finish | Branch bool bool int

fun bytesize :: "operation \<Rightarrow> nat" where
  "bytesize (Branch c wide d) = (if wide then 3 else 2)"
| "bytesize _ = 1"

fun encodable :: "operation \<Rightarrow> bool" where
  "encodable (Branch c wide d) = (if wide then -32768 \<le> d \<and> d < 32768 else -128 \<le> d \<and> d < 128)"
| "encodable _ = True"

fun encode :: "operation \<Rightarrow> nat list" where
  "encode Idle = [0]"
| "encode Raise = [1]"
| "encode Lower = [2]"
| "encode Finish = [3]"
| "encode (Branch c False d) = [if c then 17 else 16, nat (d + 128)]"
| "encode (Branch c True d) = [if c then 19 else 18, nat (d + 32768) mod 256, nat (d + 32768) div 256]"

fun decode :: "nat list \<Rightarrow> (operation \<times> nat list) option" where
  "decode [] = None"
| "decode (b # bs) =
    (if b = 0 then Some (Idle, bs)
     else if b = 1 then Some (Raise, bs)
     else if b = 2 then Some (Lower, bs)
     else if b = 3 then Some (Finish, bs)
     else if b = 16 \<or> b = 17 then
       (case bs of [] \<Rightarrow> None | x # xs \<Rightarrow>
         if x < 256 then Some (Branch (b = 17) False (int x - 128), xs) else None)
     else if b = 18 \<or> b = 19 then
       (case bs of x # y # xs \<Rightarrow>
         if x < 256 \<and> y < 256 then Some (Branch (b = 19) True (int (y * 256 + x) - 32768), xs) else None
        | _ \<Rightarrow> None)
     else None)"

lemma encode_length [simp]: "length (encode op) = bytesize op"
  by (cases op) (auto split: bool.splits)

lemma byte_join: "n div 256 * 256 + n mod 256 = (n :: nat)"
  by (simp add: div_mult_mod_eq)

lemma encode_bytes:
  "encodable op \<Longrightarrow> set (encode op) \<subseteq> {..<256}"
  by (cases op) (auto simp: nat_less_iff div_less_iff_less_mult split: bool.splits if_splits)

theorem decode_encode:
  assumes "encodable op"
  shows "decode (encode op @ tail) = Some (op, tail)"
  using assms
  by (cases op)
    (auto simp: byte_join nat_less_iff div_less_iff_less_mult split: bool.splits if_splits)

fun lower :: "nat instruction list \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat instruction \<Rightarrow> operation" where
  "lower p W i Nop = Idle"
| "lower p W i Inc = Raise"
| "lower p W i Dec = Lower"
| "lower p W i Stop = Finish"
| "lower p W i (Jump t) = Branch False (i \<in> W) (displacement p W i)"
| "lower p W i (Zero t) = Branch True (i \<in> W) (displacement p W i)"

definition chunks :: "nat instruction list \<Rightarrow> nat set \<Rightarrow> nat list list" where
  "chunks p W = map (\<lambda>i. encode (lower p W i (p ! i))) [0..<length p]"

definition bytecode :: "nat instruction list \<Rightarrow> nat set \<Rightarrow> nat list" where
  "bytecode p W = concat (chunks p W)"

lemma chunks_code [code]:
  "chunks p W = map (\<lambda>(i,op). encode (lower p W i op)) (zip [0..<length p] p)"
  unfolding chunks_def by (rule nth_equalityI) auto

lemma lower_size:
  "i < length p \<Longrightarrow> bytesize (lower p W i (p ! i)) = width p W i"
  unfolding width_def branches_def by (cases "p ! i") auto

lemma lower_encodable:
  "valid p W \<Longrightarrow> i < length p \<Longrightarrow> encodable (lower p W i (p ! i))"
  unfolding valid_def fits_signed branches_def
  by (cases "p ! i") (auto split: if_splits)

lemma chunks_length [simp]: "length (chunks p W) = length p"
  by (simp add: chunks_def)

lemma chunks_nth:
  "i < length p \<Longrightarrow> chunks p W ! i = encode (lower p W i (p ! i))"
  by (simp add: chunks_def)

lemma prefix_length:
  "i \<le> length p \<Longrightarrow> length (concat (take i (chunks p W))) = address p W i"
proof (induction i)
  case 0
  then show ?case by simp
next
  case (Suc i)
  then have idx: "i < length p" by simp
  show ?case using Suc.IH Suc.prems
    by (simp add: take_Suc_conv_app_nth chunks_nth[OF idx] lower_size[OF idx])
qed

lemma bytecode_length: "length (bytecode p W) = address p W (length p)"
  using prefix_length[of "length p" p W] by (simp add: bytecode_def)

lemma bytecode_bytes:
  assumes valid: "valid p W"
  shows "set (bytecode p W) \<subseteq> {..<256}"
proof -
  have each: "\<And>i. i < length p \<Longrightarrow> set (encode (lower p W i (p ! i))) \<subseteq> {..<256}"
    by (rule encode_bytes, rule lower_encodable[OF valid]) assumption
  show ?thesis unfolding bytecode_def chunks_def
    by (auto dest: each[THEN subsetD])
qed

lemma fetch_instruction:
  assumes "valid p W" "i < length p"
  shows "map_option fst (decode (drop (address p W i) (bytecode p W))) = Some (lower p W i (p ! i))"
proof -
  have prefix: "bytecode p W = concat (take i (chunks p W)) @ concat (drop i (chunks p W))"
    by (simp add: bytecode_def flip: concat_append)
  have suffix: "drop i (chunks p W) = chunks p W ! i # drop (Suc i) (chunks p W)"
    using assms(2) by (simp add: Cons_nth_drop_Suc)
  show ?thesis
    using prefix_length[OF less_imp_le[OF assms(2)], of W]
    by (subst prefix, subst suffix)
      (simp add: chunks_nth[OF assms(2)] decode_encode[OF lower_encodable[OF assms]])
qed

end
