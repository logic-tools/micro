theory Disjunction imports Main begin

datatype 'a form = Pro 'a | Neg \<open>'a form\<close>| Dis \<open>'a form\<close> \<open>'a form\<close>

primrec semantics where
  \<open>semantics i (Pro n) = i n\<close> |
  \<open>semantics i (Neg p) = (\<not> semantics i p)\<close> |
  \<open>semantics i (Dis p q) = (semantics i p \<or> semantics i q)\<close>

function \<mu> where
  \<open>\<mu> A B (Pro n # C) = \<mu> (n # A) B C\<close> |
  \<open>\<mu> A B (Neg (Pro n) # C) = \<mu> A (n # B) C\<close> |
  \<open>\<mu> A B (Neg (Neg p) # C) = \<mu> A B (p # C)\<close> |
  \<open>\<mu> A B (Neg (Dis p q) # C) = \<mu> A B (Neg p # C) \<union> \<mu> A B (Neg q # C)\<close> |
  \<open>\<mu> A B (Dis p q # C) = \<mu> A B (p # q # C)\<close> |
  \<open>\<mu> A B [] = (if set A \<inter> set B = {} then {B} else {})\<close>
  by pat_completeness simp_all

termination by (relation \<open>measure (\<lambda>(_, _, C). \<Sum>p \<leftarrow> C. size p)\<close>) simp_all

theorem main: \<open>(\<forall>i. \<exists>p \<in> set (map Pro A @ map (Neg \<circ> Pro) B @ C). semantics i p) \<longleftrightarrow> \<mu> A B C = {}\<close>
proof (induct rule: \<mu>.induct)
  case 6
  have 1: \<open>set A \<inter> set B = {} \<Longrightarrow> \<exists>i. \<forall>x\<in>Pro ` set A \<union> (\<lambda>a. Neg (Pro a)) ` set B.
            \<not> semantics i x\<close> for A B :: \<open>'a list\<close>
    by force
  have 2: \<open>\<forall>x\<in>Pro ` set A \<union> (\<lambda>a. Neg (Pro a)) ` set B. \<not> semantics i x \<Longrightarrow>
            x \<in> set A \<Longrightarrow> x \<in> set B \<Longrightarrow> False\<close> for i x and A B :: \<open>'a list\<close>
    by (metis UnCI imageI semantics.simps(2))
  from 6 show ?case
    by (auto dest: 1 2)
qed auto

abbreviation \<open>prover p \<equiv> \<mu> [] [] [p] = {}\<close>

corollary \<open>prover p \<longleftrightarrow> (\<forall>i. semantics i p)\<close>
  by (simp flip: main)

value \<open>prover (Dis (Pro n) (Neg (Pro n)))\<close>

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
  \<open>mp A B (Neg (Dis p q) # C) = (mp A B (Neg p # C) \<and> mp A B (Neg q # C))\<close> |
  \<open>mp A B (Dis p q # C) = mp A B (p # q # C)\<close> |
  \<open>mp A B [] = common A B\<close>
  by pat_completeness simp_all

termination by (relation \<open>measure (\<lambda>(_, _, C). \<Sum>p \<leftarrow> C. size p)\<close>) simp_all

lemma mp_iff [iff]: \<open>mp A B C \<longleftrightarrow> \<mu> A B C = {}\<close>
  by (induct rule: \<mu>.induct) auto

definition \<open>prover' p \<equiv> mp [] [] [p]\<close>

corollary \<open>prover' p \<longleftrightarrow> (\<forall>i. semantics i p)\<close>
  unfolding prover'_def by (simp flip: main)

definition \<open>main \<equiv> prover' (Dis (Pro ()) (Neg (Pro ())))\<close>

proposition main
  by code_simp

export_code main in Haskell

end
