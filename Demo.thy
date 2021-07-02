theory Demo imports Main begin

datatype 'a form = Paf 'a | Naf 'a | Con \<open>'a form\<close> \<open>'a form\<close> | Dis \<open>'a form\<close> \<open>'a form\<close>

fun val where
  \<open>val i (Paf n) = i n\<close> |
  \<open>val i (Naf n) = (\<not> i n)\<close> |
  \<open>val i (Con p q) = (val i p \<and> val i q)\<close> |
  \<open>val i (Dis p q) = (val i p \<or> val i q)\<close>

function cal where
  \<open>cal e [] = (\<exists>n \<in> fst e. n \<in> snd e)\<close> |
  \<open>cal e (Paf n # s) = cal ({n} \<union> fst e, snd e) s\<close> |
  \<open>cal e (Naf n # s) = cal (fst e, snd e \<union> {n}) s\<close> |
  \<open>cal e (Con p q # s) = (cal e (p # s) \<and> cal e (q # s))\<close> |
  \<open>cal e (Dis p q # s) = cal e (p # q # s)\<close>
  by pat_completeness simp_all

termination by (relation \<open>measure (\<lambda>(_, s). \<Sum>p \<leftarrow> s. size p)\<close>) simp_all

definition \<open>prover p \<equiv> cal ({}, {}) [p]\<close>

value \<open>map prover [Paf n, Naf n, Con (Paf n) (Naf n), Dis (Paf n) (Naf n)]\<close>

abbreviation \<open>sat i e \<equiv> (\<exists>n \<in> fst e. i n) \<or> (\<exists>n \<in> snd e. \<not> i n)\<close>

lemma sound_and_complete: \<open>cal e s \<longleftrightarrow> (\<forall>i. (\<exists>p \<in> set s. val i p) \<or> sat i e)\<close>
  by (induct rule: cal.induct) auto

theorem main: \<open>prover p \<longleftrightarrow> (\<forall>i. val i p)\<close>
  unfolding sound_and_complete prover_def by simp

end
