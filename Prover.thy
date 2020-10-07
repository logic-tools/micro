theory Prover imports Main begin

datatype 'a form = Atom bool 'a | Op \<open>'a form\<close> bool \<open>'a form\<close>

primrec val where
  \<open>val i (Atom b n) = (if b then i n else \<not> i n)\<close> |
  \<open>val i (Op p b q) = (if b then val i p \<and> val i q else val i p \<or> val i q)\<close>

function cal where
  \<open>cal e [] = (\<exists>n \<in> fst e. n \<in> snd e)\<close> |
  \<open>cal e (Atom b n # s) = (if b then cal ({n} \<union> fst e, snd e) s else cal (fst e, snd e \<union> {n}) s)\<close> |
  \<open>cal e (Op p b q # s) = (if b then cal e (p # s) \<and> cal e (q # s) else cal e (p # q # s))\<close>
  by pat_completeness auto termination by (relation \<open>measure (\<lambda>(_, s). \<Sum>p \<leftarrow> s. size p)\<close>) auto

definition \<open>prover p \<equiv> cal ({}, {}) [p]\<close>

value \<open>prover (Op (Atom True n) False (Atom False n))\<close>

lemma complete: \<open>cal e s \<longleftrightarrow> (\<forall>i. \<exists>p \<in> set s \<union> Atom True ` fst e \<union> Atom False ` snd e. val i p)\<close>
  unfolding bex_Un by (induct rule: cal.induct) (auto split: if_split)

theorem \<open>prover p \<longleftrightarrow> (\<forall>i. val i p)\<close>
  unfolding complete prover_def by auto

end
