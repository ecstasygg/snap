theory Machine
  imports Encoding
begin

fun machine_advance :: "operation \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "machine_advance Idle pc a = Some (Suc pc, a)"
| "machine_advance Raise pc a = Some (Suc pc, Suc a)"
| "machine_advance Lower pc a = Some (Suc pc, a - 1)"
| "machine_advance Finish pc a = None"
| "machine_advance (Branch c wide d) pc a =
    (let next = pc + (if wide then 3 else 2) in
     if c \<and> a \<noteq> 0 then Some (next, a)
     else if 0 \<le> int next + d then Some (nat (int next + d), a) else None)"

definition machine_step :: "nat list \<Rightarrow> nat \<times> nat \<Rightarrow> (nat \<times> nat) option" where
  "machine_step code s = (case map_option fst (decode (drop (fst s) code)) of
     None \<Rightarrow> None | Some op \<Rightarrow> machine_advance op (fst s) (snd s))"

definition relocate :: "nat instruction list \<Rightarrow> nat set \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat" where
  "relocate p W s = (address p W (fst s), snd s)"

lemma lower_advance:
  assumes "i < length p"
  shows "machine_advance (lower p W i (p ! i)) (address p W i) a =
    map_option (relocate p W) (advance (p ! i) i a)"
  using assms unfolding relocate_def
  by (cases "p ! i")
    (auto simp: displacement_def destination_def width_def branches_def Let_def of_nat_add)

lemma source_closed:
  "wellformed p \<Longrightarrow> i \<le> length p \<Longrightarrow> source_step p (i,a) = Some (j,b) \<Longrightarrow> j \<le> length p"
  unfolding wellformed_def source_step_def branches_def destination_def
  by (cases "p ! i") (auto split: if_splits)

theorem step_correspondence:
  assumes "valid p W" "i \<le> length p"
  shows "machine_step (bytecode p W) (relocate p W (i,a)) =
    map_option (relocate p W) (source_step p (i,a))"
proof (cases "i < length p")
  case True
  show ?thesis using fetch_instruction[OF assms(1) True] lower_advance[OF True, of W a] True
    by (auto simp: machine_step_def source_step_def relocate_def split: option.splits prod.splits)
next
  case False
  with assms have "i = length p" by simp
  then show ?thesis
    by (simp add: machine_step_def source_step_def relocate_def bytecode_length[symmetric])
qed

theorem execution_correspondence:
  assumes "wellformed p" "valid p W" "i \<le> length p"
  shows "execute (machine_step (bytecode p W)) fuel (relocate p W (i,a)) =
    relocate p W (execute (source_step p) fuel (i,a))"
  using assms(3)
proof (induction fuel arbitrary: i a)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
    using Suc.IH source_closed[OF assms(1) Suc.prems]
      step_correspondence[OF assms(2) Suc.prems, of a]
    by (cases "source_step p (i,a)") (auto split: prod.splits)
qed

definition assemble :: "nat instruction list \<Rightarrow> nat list option" where
  "assemble p = (if wellformed p \<and> valid p (layout p) then Some (bytecode p (layout p)) else None)"

theorem assembly_complete:
  "assemble p \<noteq> None \<longleftrightarrow> wellformed p \<and> (\<exists>W. valid p W)"
  by (simp add: assemble_def layout_complete)

theorem assembly_minimum:
  "assemble p = Some code \<Longrightarrow> valid p V \<Longrightarrow> length code \<le> address p V (length p)"
  using layout_minimum[of p V] by (auto simp: assemble_def bytecode_length split: if_splits)

theorem assembly_execution:
  assumes "assemble p = Some code"
  shows "execute (machine_step code) fuel (0,a) =
    relocate p (layout p) (execute (source_step p) fuel (0,a))"
  using assms execution_correspondence[of p "layout p" 0 fuel a]
  by (auto simp: assemble_def relocate_def split: if_splits)

end
