theory propositional_exercise
imports FOL PropLib
begin

section "Superman does not exist"

lemma mpInverse:"\<lbrakk>\<not>P;Q\<longrightarrow>P\<rbrakk>\<Longrightarrow>\<not>Q"
  thm contrapos
  apply(drule contrapos[where Q="P" and P="Q"])
  thm mp
  apply(drule mp)
  apply assumption+
  done

lemma stepOne:"\<lbrakk>\<not>A\<longrightarrow>I; \<not>W\<longrightarrow>M;\<not>(A\<and>W)\<rbrakk>\<Longrightarrow>(I\<or>M)"
  thm  disj_mono
  thm de_Morgan_conj
  apply(drule disj_mono)
  apply assumption
  apply(unfold de_Morgan_conj)
  thm mp
  apply(drule mp[where P=" \<not> A \<or> \<not> W"])
  apply assumption+
  done

lemma OREli:"\<lbrakk>E\<or>\<not>P;P\<rbrakk>\<Longrightarrow>E"
  thm disj_commute
  apply(unfold disj_commute[where P="E" and Q = "\<not>P"])
  thm not_disj_iff_imp
  apply(unfold not_disj_iff_imp)
  thm mp
  apply(rule mp)
  apply assumption+
  done


theorem "\<lbrakk>A\<and>W\<longrightarrow> P;\<not>A\<longrightarrow>I;\<not>W\<longrightarrow>M;\<not>P;E\<longrightarrow>(\<not>I\<and>\<not>M)\<rbrakk> \<Longrightarrow>\<not>E"
  thm notI
  thm de_Morgan_disj
  apply(fold de_Morgan_disj)
  apply(drule mpInverse[where Q="A\<and>W"])
  apply assumption
  apply(drule stepOne)
    apply assumption+
  apply(drule  impI2'[where P="E"])
  apply(rule OREli[where P="I \<or> M"])
  apply assumption+
  done

section "Portia's suitor's dilemma"

lemma mpbi:"\<lbrakk>(A\<longleftrightarrow>B);\<not>B\<rbrakk>\<Longrightarrow>\<not>A"
  apply(unfold iff_def)
  apply(drule conjE[where P="(A \<longrightarrow> B)" and Q="(B \<longrightarrow> A)" and R="\<not>A"] )
  thm mpInverse
   apply(rule mpInverse[where P="B" ])
    apply assumption+
  done

lemma iff_red1 :  "A \<longleftrightarrow> B \<Longrightarrow> \<not> A \<Longrightarrow> \<not> B"
  thm iff_def
  apply(unfold iff_def)
  thm IFOL.conjunct2
  apply(drule IFOL.conjunct2[where P="A\<longrightarrow>B"])
  thm mpInverse
  apply(rule mpInverse[where P="A"])
   apply assumption+
  done  

lemma iff_red2: "\<lbrakk>A\<longleftrightarrow>\<not>B\<rbrakk> \<Longrightarrow>\<not>B\<longrightarrow>A"
  thm iff_def
  apply(unfold iff_def[where P="A"])
  thm conjE
  apply(rule conjE[where P="A\<longrightarrow>\<not>B" and Q="\<not>B\<longrightarrow>A"])
  apply assumption+
  done

lemma test:"\<lbrakk>S\<longleftrightarrow>\<not>(S\<longleftrightarrow>G)\<rbrakk>\<Longrightarrow>\<not>G"
  apply(unfold FOL.not_iff)
  apply(rule iff_red1[where A="S"])
  apply auto

  done


theorem "\<lbrakk>\<not>(PG\<longleftrightarrow>PS);G\<longleftrightarrow>\<not>PG;S\<longleftrightarrow>(\<not>(S\<longleftrightarrow>G))\<rbrakk> \<Longrightarrow>PG"
  thm iff_red2
  apply(drule iff_red2)
  thm   impI2'
  apply(drule  impI2')
  thm test
  apply(drule test)

  thm not_disj_iff_imp
  apply(unfold not_disj_iff_imp)

  thm mpInverse

  apply(drule mpInverse[where P="G" and  Q="\<not>PG"])
  apply assumption
  thm notnotD
   apply(rule notnotD)
  apply assumption+
  done

end