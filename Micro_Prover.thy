theory Micro_Prover imports Main begin

datatype 'a form = Pro 'a | Falsity (\<open>\<bottom>\<close>) | Imp \<open>'a form\<close> \<open>'a form\<close> (infix \<open>\<rightarrow>\<close> 0)

primrec semantics where
  \<open>semantics i (Pro n) = i n\<close> |
  \<open>semantics _ \<bottom> = False\<close> |
  \<open>semantics i (p \<rightarrow> q) = (semantics i p \<longrightarrow> semantics i q)\<close>

abbreviation \<open>sc X Y i \<equiv> (\<forall>p \<in> set X. semantics i p) \<longrightarrow> (\<exists>q \<in> set Y. semantics i q)\<close>

function \<mu> where
  \<open>\<mu> A B (Pro n # C) [] = \<mu> (n # A) B C []\<close> |
  \<open>\<mu> A B C (Pro n # D) = \<mu> A (n # B) C D\<close> |
  \<open>\<mu> _ _ (\<bottom> # _) [] = {}\<close> |
  \<open>\<mu> A B C (\<bottom> # D) = \<mu> A B C D\<close> |
  \<open>\<mu> A B ((p \<rightarrow> q) # C) [] = \<mu> A B C [p] \<union> \<mu> A B (q # C) []\<close> |
  \<open>\<mu> A B C ((p \<rightarrow> q) # D) = \<mu> A B (p # C) (q # D)\<close> |
  \<open>\<mu> A B [] [] = (if set A \<inter> set B = {} then {A} else {})\<close>
  by pat_completeness simp_all

termination by (relation \<open>measure (\<lambda>(_,_,C,D). \<Sum>p \<leftarrow> C @ D. size p)\<close>) simp_all

lemma sat: \<open>sc (map Pro A @ C) (map Pro B @ D) (\<lambda>n. n \<in> set L) \<Longrightarrow> L \<notin> \<mu> A B C D\<close>
  by (induct rule: \<mu>.induct) auto

theorem main: \<open>(\<forall>i. sc (map Pro A @ C) (map Pro B @ D) i) \<longleftrightarrow> \<mu> A B C D = {}\<close>
  by (induct rule: \<mu>.induct) (auto simp: sat)

primrec member where
  \<open>member _ [] = False\<close> |
  \<open>member m (n # A) = (if m = n then True else member m A)\<close>

lemma member_iff [iff]: \<open>member m A \<longleftrightarrow> m \<in> set A\<close>
  by (induct A) simp_all

primrec common where
  \<open>common _ [] = False\<close> |
  \<open>common A (m # B) = (if member m A then True else common A B)\<close>

lemma common_iff [iff]: \<open>common A B \<longleftrightarrow> set A \<inter> set B \<noteq> {}\<close>
  by (induct B) simp_all

function mp where
  \<open>mp A B (Pro n # C) [] = mp (n # A) B C []\<close> |
  \<open>mp A B C (Pro n # D) = mp A (n # B) C D\<close> |
  \<open>mp _ _ (Falsity # _) [] = True\<close> |
  \<open>mp A B C (Falsity # D) = mp A B C D\<close> |
  \<open>mp A B (Imp p q # C) [] = (if mp A B C [p] then mp A B (q # C) [] else False)\<close> |
  \<open>mp A B C (Imp p q # D) = mp A B (p # C) (q # D)\<close> |
  \<open>mp A B [] [] = common A B\<close>
  by pat_completeness simp_all

termination by (relation \<open>measure (\<lambda>(_,_,C,D). \<Sum>p \<leftarrow> C @ D. size p)\<close>) simp_all

lemma mp_iff [iff]: \<open>mp A B C D \<longleftrightarrow> \<mu> A B C D = {}\<close>
  by (induct rule: \<mu>.induct) simp_all

definition \<open>prover p \<equiv> mp [] [] [] [p]\<close>

corollary \<open>prover p \<longleftrightarrow> (\<forall>i. semantics i p)\<close>
  unfolding prover_def by (simp flip: main)

end
