theory Relax
  imports Layout
begin

definition pending :: "nat instruction list \<Rightarrow> nat set \<Rightarrow> nat set" where
  "pending p W = {i \<in> branches p. i \<notin> W \<and> \<not> fits p W i 8}"

definition widen :: "nat instruction list \<Rightarrow> nat set \<Rightarrow> nat set" where
  "widen p W = W \<union> pending p W"

lemma widen_extensive: "W \<subseteq> widen p W"
  by (auto simp: widen_def)

lemma widen_bounded:
  "W \<subseteq> branches p \<Longrightarrow> widen p W \<subseteq> branches p"
  by (auto simp: widen_def pending_def)

lemma widen_decreases:
  assumes "widen p W \<noteq> W"
  shows "card (branches p - widen p W) < card (branches p - W)"
proof (rule psubset_card_mono)
  show "finite (branches p - W)" by simp
  show "branches p - widen p W \<subset> branches p - W"
    using assms unfolding widen_def pending_def by auto
qed

function settle :: "nat instruction list \<Rightarrow> nat set \<Rightarrow> nat set" where
  "settle p W = (if widen p W = W then W else settle p (widen p W))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(p,W). card (branches p - W))")
    (auto intro: widen_decreases)

declare settle.simps [simp del]

lemma settle_fixed: "widen p (settle p W) = settle p W"
  by (induction p W rule: settle.induct) (subst (1 2) settle.simps, auto)

lemma settle_extensive: "W \<subseteq> settle p W"
proof (induction p W rule: settle.induct)
  case (1 p W)
  show ?case
  proof (cases "widen p W = W")
    case True
    show ?thesis by (subst settle.simps) (simp add: True)
  next
    case False
    have "widen p W \<subseteq> settle p (widen p W)" using "1.IH" False by simp
    then have sub: "W \<subseteq> settle p (widen p W)" using widen_extensive[of W p] by blast
    show ?thesis by (subst settle.simps) (simp add: False sub)
  qed
qed

lemma settle_bounded:
  "W \<subseteq> branches p \<Longrightarrow> settle p W \<subseteq> branches p"
proof (induction p W rule: settle.induct)
  case (1 p W)
  show ?case
  proof (cases "widen p W = W")
    case True
    show ?thesis by (subst settle.simps) (simp add: True "1.prems")
  next
    case False
    have bounded: "widen p W \<subseteq> branches p" by (rule widen_bounded[OF "1.prems"])
    have rec: "settle p (widen p W) \<subseteq> branches p" by (rule "1.IH"[OF False bounded])
    show ?thesis by (subst settle.simps) (simp add: False rec)
  qed
qed

lemma widen_necessary:
  assumes "valid p V" "W \<subseteq> V"
  shows "widen p W \<subseteq> V"
proof
  fix i
  assume member: "i \<in> widen p W"
  show "i \<in> V"
  proof (cases "i \<in> W")
    case True
    with assms show ?thesis by blast
  next
    case False
    with member have branch: "i \<in> branches p" and bad: "\<not> fits p W i 8"
      by (auto simp: widen_def pending_def)
    show ?thesis
    proof (rule ccontr)
      assume "i \<notin> V"
      with assms(1) branch have "fits p V i 8" by (auto simp: valid_def)
      then have "fits p W i 8" by (rule fits_downward[OF assms(2)])
      with bad show False by contradiction
    qed
  qed
qed

lemma settle_least:
  assumes "valid p V" "W \<subseteq> V"
  shows "settle p W \<subseteq> V"
  using assms
proof (induction p W rule: settle.induct)
  case (1 p W)
  show ?case
  proof (cases "widen p W = W")
    case True
    show ?thesis by (subst settle.simps) (simp add: True "1.prems")
  next
    case False
    have necessary: "widen p W \<subseteq> V" by (rule widen_necessary[OF "1.prems"])
    have rec: "settle p (widen p W) \<subseteq> V" by (rule "1.IH"[OF False "1.prems"(1) necessary])
    show ?thesis by (subst settle.simps) (simp add: False rec)
  qed
qed

definition layout :: "nat instruction list \<Rightarrow> nat set" where
  "layout p = settle p {}"

lemma layout_bounded: "layout p \<subseteq> branches p"
  unfolding layout_def by (rule settle_bounded) simp

lemma layout_least: "valid p V \<Longrightarrow> layout p \<subseteq> V"
  unfolding layout_def by (rule settle_least) auto

lemma layout_short:
  "i \<in> branches p \<Longrightarrow> i \<notin> layout p \<Longrightarrow> fits p (layout p) i 8"
  using settle_fixed[of p "{}"] unfolding layout_def widen_def pending_def by auto

theorem layout_complete:
  "valid p (layout p) \<longleftrightarrow> (\<exists>V. valid p V)"
proof
  assume "valid p (layout p)"
  then show "\<exists>V. valid p V" by blast
next
  assume "\<exists>V. valid p V"
  then obtain V where v: "valid p V" by blast
  have sub: "layout p \<subseteq> V" by (rule layout_least[OF v])
  have "\<forall>i\<in>branches p. fits p (layout p) i (if i \<in> layout p then 16 else 8)"
    using v sub layout_short fits_downward[OF sub]
    unfolding valid_def by (auto split: if_splits)
  with layout_bounded show "valid p (layout p)" by (simp add: valid_def)
qed

theorem layout_minimum:
  "valid p V \<Longrightarrow> address p (layout p) (length p) \<le> address p V (length p)"
  by (intro address_mono layout_least)

end
