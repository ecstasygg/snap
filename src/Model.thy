theory Model
  imports Main
begin

datatype 'a instruction = Nop | Inc | Dec | Stop | Jump 'a | Zero 'a

fun target :: "'a instruction \<Rightarrow> 'a option" where
  "target (Jump t) = Some t"
| "target (Zero t) = Some t"
| "target _ = None"

definition branches :: "nat instruction list \<Rightarrow> nat set" where
  "branches p = {i. i < length p \<and> target (p ! i) \<noteq> None}"

definition destination :: "nat instruction list \<Rightarrow> nat \<Rightarrow> nat" where
  "destination p i = the (target (p ! i))"

definition wellformed :: "nat instruction list \<Rightarrow> bool" where
  "wellformed p \<longleftrightarrow> (\<forall>i \<in> branches p. destination p i < length p)"

lemma finite_branches [simp]: "finite (branches p)"
  unfolding branches_def by (rule finite_subset[of _ "{..<length p}"]) auto

lemma branch_index: "i \<in> branches p \<Longrightarrow> i < length p"
  by (simp add: branches_def)

lemma branches_code [code]:
  "branches p = set (map fst (filter (\<lambda>(i,op). target op \<noteq> None) (zip [0..<length p] p)))"
  by (auto simp: branches_def set_zip image_iff; force)

fun advance :: "nat instruction \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "advance Nop i a = Some (Suc i, a)"
| "advance Inc i a = Some (Suc i, Suc a)"
| "advance Dec i a = Some (Suc i, a - 1)"
| "advance Stop i a = None"
| "advance (Jump t) i a = Some (t, a)"
| "advance (Zero t) i a = Some (if a = 0 then t else Suc i, a)"

definition source_step :: "nat instruction list \<Rightarrow> nat \<times> nat \<Rightarrow> (nat \<times> nat) option" where
  "source_step p s = (if fst s < length p then advance (p ! fst s) (fst s) (snd s) else None)"

fun execute :: "('s \<Rightarrow> 's option) \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> 's" where
  "execute step 0 s = s"
| "execute step (Suc n) s = (case step s of None \<Rightarrow> s | Some t \<Rightarrow> execute step n t)"

end
