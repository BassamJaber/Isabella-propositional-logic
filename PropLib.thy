theory PropLib
imports FOL
begin

theorem FalseI: "\<not> P \<and> P \<Longrightarrow> False"
  apply(rule mp[where P="\<not>P \<and> P"])

    --\<open>first goal @{term "\<not> P \<and> P \<longrightarrow> False"}\<close>
    apply(rule conjunct1[where Q="False \<longrightarrow> \<not> P \<and> P"])
    apply(fold iff_def)
    apply(rule FOL.IFOL_simps(9))
    
    --\<open>second goal @{term "\<not> P \<and> P"}\<close>
    apply(assumption)
  done


lemma impI2': "P \<longrightarrow> Q \<Longrightarrow> \<not> P \<or> Q"
  apply(unfold not_disj_iff_imp)
  apply(assumption)
  done

lemma disjE2: "A \<or> A \<Longrightarrow> A"
  apply(erule disjE)
  apply(assumption)+
  done

lemma disjE2': "\<not>\<not>A \<or> A \<Longrightarrow> A"
  apply(erule disjE)
  apply(rule notnotD)
  apply(assumption)+
  done

theorem add1: "(A \<longleftrightarrow> \<not> A) \<longleftrightarrow> False"
  apply(unfold iff_def)
  apply(rule conjI)
    --\<open>first goal\<close>
    apply(rule impI)
    apply(rule FalseI[where P="A"])
    apply(rule conjI)
      --\<open>first goal\<close>
      apply(erule conjE[where P="(A \<longrightarrow> \<not> A)" and Q="(\<not> A \<longrightarrow> A)"])
      apply(rule disjE2)
      apply(rule impI2')
      apply(assumption)
      --\<open>second goal\<close>
      apply(erule conjE)
      apply(rule disjE2')
      apply(rule impI2')
      apply(assumption)
    --\<open>second goal\<close>
    apply(rule impI)
    apply(erule FalseE)
  done

end