theory Conjunction imports Main begin

datatype 'a form = Pro 'a | Neg \<open>'a form\<close>| Con \<open>'a form\<close> \<open>'a form\<close>

primrec semantics where
  \<open>semantics i (Pro n) = i n\<close> |
  \<open>semantics i (Neg p) = (\<not> semantics i p)\<close> |
  \<open>semantics i (Con p q) = (semantics i p \<and> semantics i q)\<close>

function \<mu> where
  \<open>\<mu> A B (Pro n # C) = \<mu> (n # A) B C\<close> |
  \<open>\<mu> A B (Neg (Pro n) # C) = \<mu> A (n # B) C\<close> |
  \<open>\<mu> A B (Neg (Neg p) # C) = \<mu> A B (p # C)\<close> |
  \<open>\<mu> A B (Neg (Con p q) # C) = \<mu> A B (Neg p # Neg q # C)\<close> |
  \<open>\<mu> A B (Con p q # C) = \<mu> A B (p # C) \<union> \<mu> A B (q # C)\<close> |
  \<open>\<mu> A B [] = (if \<exists>n \<in> set A. n \<in> set B then {} else {B})\<close>
  by pat_completeness simp_all

primrec sz where
  \<open>sz (Pro _) = 1\<close> |
  \<open>sz (Neg p) = 1 + sz p\<close> |
  \<open>sz (Con p q) = 2 + sz p + sz q\<close>

termination by (relation \<open>measure (\<lambda>(_, _, C). (\<Sum>p \<leftarrow> C. sz p))\<close>) simp_all

theorem main: \<open>(\<forall>i. \<exists>p \<in> set (map Pro A @ map (Neg \<circ> Pro) B @ C). semantics i p) \<longleftrightarrow> \<mu> A B C = {}\<close>
proof (induct rule: \<mu>.induct)
  case 6
  have 1: \<open>n \<in> set A \<Longrightarrow> n \<in> set B \<Longrightarrow> \<exists>x \<in> Pro ` set A \<union> (\<lambda>a. Neg (Pro a)) ` set B.
            semantics i x\<close> for n i and A B :: \<open>'a list\<close>
    by (metis UnCI imageI semantics.simps(2))
  have 2: \<open>\<forall>n \<in> set A. n \<notin> set B \<Longrightarrow> \<exists>i. \<forall>x \<in> Pro ` set A \<union> (\<lambda>a. Neg (Pro a)) ` set B.
            \<not> semantics i x\<close> for A B :: \<open>'a list\<close>
    by (metis (mono_tags, lifting) Un_iff imageE in_set_member semantics.simps(1,2))
  from 6 show ?case
    by (auto dest: 1 2)
qed auto

abbreviation \<open>prover p \<equiv> \<mu> [] [] [p] = {}\<close>

corollary \<open>prover p \<longleftrightarrow> (\<forall>i. semantics i p)\<close>
  by (simp flip: main)

value \<open>prover (Neg (Con (Pro n) (Neg (Pro n))))\<close>

primrec member where
  \<open>member _ [] = False\<close> |
  \<open>member m (n # A) = (m = n \<or> member m A)\<close>

lemma member_iff [iff]: \<open>member m A \<longleftrightarrow> m \<in> set A\<close>
  by (induct A) simp_all

primrec common where
  \<open>common _ [] = False\<close> |
  \<open>common A (m # B) = (member m A \<or> common A B)\<close>

lemma common_iff [iff]: \<open>common A B \<longleftrightarrow> (\<exists>n \<in> set A. n \<in> set B)\<close>
  by (induct B) auto

function mp where
  \<open>mp A B (Pro n # C) = mp (n # A) B C\<close> |
  \<open>mp A B (Neg (Pro n) # C) = mp A (n # B) C\<close> |
  \<open>mp A B (Neg (Neg p) # C) = mp A B (p # C)\<close> |
  \<open>mp A B (Neg (Con p q) # C) = mp A B (Neg p # Neg q # C)\<close> |
  \<open>mp A B (Con p q # C) = (mp A B (p # C) \<and> mp A B (q # C))\<close> |
  \<open>mp A B [] = common A B\<close>
  by pat_completeness simp_all

termination by (relation \<open>measure (\<lambda>(_, _, C). (\<Sum>p \<leftarrow> C. sz p))\<close>) simp_all

lemma mp_iff [iff]: \<open>mp A B C \<longleftrightarrow> \<mu> A B C = {}\<close>
  by (induct rule: \<mu>.induct) simp_all

definition \<open>prover' p \<equiv> mp [] [] [p]\<close>

corollary \<open>prover' p \<longleftrightarrow> (\<forall>i. semantics i p)\<close>
  unfolding prover'_def by (simp flip: main)

definition \<open>main \<equiv> prover' (Neg (Con (Pro ()) (Neg (Pro ()))))\<close>

proposition main
  by code_simp

export_code main in Haskell

end
