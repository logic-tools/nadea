section \<open>Natural Deduction Assistant (NaDeA)\<close>

text \<open>
Authors: Andreas Halkjær From, Anders Schlichtkrull & Jørgen Villadsen

License: https://www.isa-afp.org/LICENSE
\<close>

theory Natural_Deduction_Assistant imports Main begin

section \<open>Natural Deduction\<close>

type_synonym id = \<open>char list\<close>

datatype tm = Var nat | Fun id \<open>tm list\<close>

datatype fm = Falsity | Pre id \<open>tm list\<close> | Imp fm fm | Dis fm fm | Con fm fm | Exi fm | Uni fm

primrec
  semantics_term :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> tm \<Rightarrow> 'a\<close> and
  semantics_list :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> tm list \<Rightarrow> 'a list\<close> where
  \<open>semantics_term e f (Var n) = e n\<close> |
  \<open>semantics_term e f (Fun i l) = f i (semantics_list e f l)\<close> |
  \<open>semantics_list e f [] = []\<close> |
  \<open>semantics_list e f (t # l) = semantics_term e f t # semantics_list e f l\<close>

primrec
  semantics :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> fm \<Rightarrow> bool\<close> where
  \<open>semantics e f g Falsity = False\<close> |
  \<open>semantics e f g (Pre i l) = g i (semantics_list e f l)\<close> |
  \<open>semantics e f g (Imp p q) = (if semantics e f g p then semantics e f g q else True)\<close> |
  \<open>semantics e f g (Dis p q) = (if semantics e f g p then True else semantics e f g q)\<close> |
  \<open>semantics e f g (Con p q) = (if semantics e f g p then semantics e f g q else False)\<close> |
  \<open>semantics e f g (Exi p) = (\<exists>x. semantics (\<lambda>n. if n = 0 then x else e (n - 1)) f g p)\<close> |
  \<open>semantics e f g (Uni p) = (\<forall>x. semantics (\<lambda>n. if n = 0 then x else e (n - 1)) f g p)\<close>

primrec member :: \<open>fm \<Rightarrow> fm list \<Rightarrow> bool\<close> where
  \<open>member p [] = False\<close> |
  \<open>member p (q # z) = (if p = q then True else member p z)\<close>

primrec
  new_term :: \<open>id \<Rightarrow> tm \<Rightarrow> bool\<close> and
  new_list :: \<open>id \<Rightarrow> tm list \<Rightarrow> bool\<close> where
  \<open>new_term c (Var n) = True\<close> |
  \<open>new_term c (Fun i l) = (if i = c then False else new_list c l)\<close> |
  \<open>new_list c [] = True\<close> |
  \<open>new_list c (t # l) = (if new_term c t then new_list c l else False)\<close>

primrec new :: \<open>id \<Rightarrow> fm \<Rightarrow> bool\<close> where
  \<open>new c Falsity = True\<close> |
  \<open>new c (Pre i l) = new_list c l\<close> |
  \<open>new c (Imp p q) = (if new c p then new c q else False)\<close> |
  \<open>new c (Dis p q) = (if new c p then new c q else False)\<close> |
  \<open>new c (Con p q) = (if new c p then new c q else False)\<close> |
  \<open>new c (Exi p) = new c p\<close> |
  \<open>new c (Uni p) = new c p\<close>

primrec news :: \<open>id \<Rightarrow> fm list \<Rightarrow> bool\<close> where
  \<open>news c [] = True\<close> |
  \<open>news c (p # z) = (if new c p then news c z else False)\<close>

primrec
  inc_term :: \<open>tm \<Rightarrow> tm\<close> and
  inc_list :: \<open>tm list \<Rightarrow> tm list\<close> where
  \<open>inc_term (Var n) = Var (n + 1)\<close> |
  \<open>inc_term (Fun i l) = Fun i (inc_list l)\<close> |
  \<open>inc_list [] = []\<close> |
  \<open>inc_list (t # l) = inc_term t # inc_list l\<close>

primrec
  sub_term :: \<open>nat \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm\<close> and
  sub_list :: \<open>nat \<Rightarrow> tm \<Rightarrow> tm list \<Rightarrow> tm list\<close> where
  \<open>sub_term v s (Var n) = (if n < v then Var n else if n = v then s else Var (n - 1))\<close> |
  \<open>sub_term v s (Fun i l) = Fun i (sub_list v s l)\<close> |
  \<open>sub_list v s [] = []\<close> |
  \<open>sub_list v s (t # l) = sub_term v s t # sub_list v s l\<close>

primrec sub :: \<open>nat \<Rightarrow> tm \<Rightarrow> fm \<Rightarrow> fm\<close> where
  \<open>sub v s Falsity = Falsity\<close> |
  \<open>sub v s (Pre i l) = Pre i (sub_list v s l)\<close> |
  \<open>sub v s (Imp p q) = Imp (sub v s p) (sub v s q)\<close> |
  \<open>sub v s (Dis p q) = Dis (sub v s p) (sub v s q)\<close> |
  \<open>sub v s (Con p q) = Con (sub v s p) (sub v s q)\<close> |
  \<open>sub v s (Exi p) = Exi (sub (v + 1) (inc_term s) p)\<close> |
  \<open>sub v s (Uni p) = Uni (sub (v + 1) (inc_term s) p)\<close>

inductive OK :: \<open>fm \<Rightarrow> fm list \<Rightarrow> bool\<close> where
  Assume: \<open>member p z \<Longrightarrow> OK p z\<close> |
  Boole: \<open>OK Falsity ((Imp p Falsity) # z) \<Longrightarrow> OK p z\<close> |
  Imp_E: \<open>OK (Imp p q) z \<Longrightarrow> OK p z \<Longrightarrow> OK q z\<close> |
  Imp_I: \<open>OK q (p # z) \<Longrightarrow> OK (Imp p q) z\<close> |
  Dis_E: \<open>OK (Dis p q) z \<Longrightarrow> OK r (p # z) \<Longrightarrow> OK r (q # z) \<Longrightarrow> OK r z\<close> |
  Dis_I1: \<open>OK p z \<Longrightarrow> OK (Dis p q) z\<close> |
  Dis_I2: \<open>OK q z \<Longrightarrow> OK (Dis p q) z\<close> |
  Con_E1: \<open>OK (Con p q) z \<Longrightarrow> OK p z\<close> |
  Con_E2: \<open>OK (Con p q) z \<Longrightarrow> OK q z\<close> |
  Con_I: \<open>OK p z \<Longrightarrow> OK q z \<Longrightarrow> OK (Con p q) z\<close> |
  Exi_E: \<open>OK (Exi p) z \<Longrightarrow> OK q ((sub 0 (Fun c []) p) # z) \<Longrightarrow> news c (p # q # z) \<Longrightarrow> OK q z\<close> |
  Exi_I: \<open>OK (sub 0 t p) z \<Longrightarrow> OK (Exi p) z\<close> |
  Uni_E: \<open>OK (Uni p) z \<Longrightarrow> OK (sub 0 t p) z\<close> |
  Uni_I: \<open>OK (sub 0 (Fun c []) p) z \<Longrightarrow> news c (p # z) \<Longrightarrow> OK (Uni p) z\<close>

section \<open>Examples\<close>

lemma \<open>OK (Imp (Pre ''p'' []) (Pre ''p'' [])) []\<close>
  by (rule Imp_I, rule Assume) simp

lemma \<open>OK (Imp (Pre ''p'' []) (Pre ''p'' [])) []\<close>
proof -
  have \<open>OK (Pre ''p'' []) [(Pre ''p'' [])]\<close> by (rule Assume) simp
  then show \<open>OK (Imp (Pre ''p'' []) (Pre ''p'' [])) []\<close> by (rule Imp_I)
qed

lemma modus_tollens: \<open>OK (Imp
  (Con (Imp (Pre ''p'' []) (Pre ''q'' [])) (Imp (Pre ''q'' []) Falsity))
  (Imp (Pre ''p'' []) Falsity)) []\<close>
  apply (rule Imp_I)
  apply (rule Imp_I)
  apply (rule Imp_E)
   apply (rule Con_E2)
   apply (rule Assume)
   apply simp
  apply (rule Imp_E)
   apply (rule Con_E1)
   apply (rule Assume)
   apply simp
  apply (rule Assume)
  apply simp
  done

lemma Socrates_is_mortal: \<open>OK (Imp
  (Con (Uni (Imp (Pre ''h'' [Var 0]) (Pre ''m'' [Var 0])))
       (Pre ''h'' [Fun ''s'' []]))
  (Pre ''m'' [Fun ''s'' []])) []\<close>
  apply (rule Imp_I)
  apply (rule Imp_E [where p=\<open>Pre ''h'' [Fun ''s'' []]\<close>])
   apply (subgoal_tac \<open>OK (sub 0 (Fun ''s'' [])
      (Imp (Pre ''h'' [Var 0]) (Pre ''m'' [Var 0]))) _\<close>)
    apply simp
   apply (rule Uni_E)
   apply (rule Con_E1)
   apply (rule Assume)
   apply simp
  apply (rule Con_E2)
  apply (rule Assume)
  apply simp
  done

lemma grandfather: \<open>OK (Imp
  (Uni (Imp (Imp (Pre ''r'' [Var 0]) Falsity) (Pre ''r'' [Fun ''f'' [Var 0]])))
  (Exi (Con (Pre ''r'' [Var 0]) (Pre ''r'' [Fun ''f'' [Fun ''f'' [Var 0]]])))) []\<close>
proof -
  let ?a = \<open>Fun ''a'' []\<close>
  let ?fa = \<open>Fun ''f'' [?a]\<close>
  let ?ffa = \<open>Fun ''f'' [?fa]\<close>
  let ?fffa = \<open>Fun ''f'' [?ffa]\<close>
  let ?ffffa = \<open>Fun ''f'' [?fffa]\<close>

  let ?ra = \<open>Pre ''r'' [?a]\<close>
  let ?rfa = \<open>Pre ''r'' [?fa]\<close>
  let ?rffa = \<open>Pre ''r'' [?ffa]\<close>
  let ?rfffa = \<open>Pre ''r'' [?fffa]\<close>
  let ?rffffa = \<open>Pre ''r'' [?ffffa]\<close>

  show ?thesis
    apply (rule Boole)
    apply (rule Imp_E)
     apply (rule Assume)
     apply simp
    apply (rule Imp_I)
    apply (rule Imp_E [where p=\<open>Imp (Imp ?ra Falsity) ?rfa\<close>])
     apply (rule Imp_I)
     apply (rule Imp_E [where p=\<open>(Imp (Imp ?rfa Falsity) ?rffa)\<close>])
      apply (rule Imp_I)
      apply (rule Imp_E [where p=\<open>Imp (Imp ?rffa Falsity) ?rfffa\<close>])
       apply (rule Imp_I)
       apply (rule Imp_E [where p=\<open>Imp (Imp ?rfffa Falsity) ?rffffa\<close>])
        apply (rule Imp_I)
        apply (rule Dis_E [where p=\<open>?ra\<close> and q=\<open>Imp ?ra Falsity\<close>])
          apply (rule Boole)
          apply (rule Imp_E [where p=\<open>Dis ?ra (Imp ?ra Falsity)\<close>])
           apply (rule Assume)
           apply simp
          apply (rule Dis_I2)
          apply (rule Imp_I)
          apply (rule Imp_E [where p=\<open>Dis ?ra (Imp ?ra Falsity)\<close>])
           apply (rule Assume)
           apply simp
          apply (rule Dis_I1)
          apply (rule Assume)
          apply simp
         apply (rule Dis_E [where p=\<open>?rffa\<close> and q=\<open>Imp ?rffa Falsity\<close>])
           apply (rule Boole)
           apply (rule Imp_E [where p=\<open>Dis ?rffa (Imp ?rffa Falsity)\<close>])
            apply (rule Assume)
            apply simp
           apply (rule Dis_I2)
           apply (rule Imp_I)
           apply (rule Imp_E [where p=\<open>Dis ?rffa (Imp ?rffa Falsity)\<close>])
            apply (rule Assume)
            apply simp
           apply (rule Dis_I1)
           apply (rule Assume)
           apply simp
          apply (rule Exi_I [where t=\<open>?a\<close>])
          apply simp
          apply (rule Con_I)
           apply (rule Assume)
           apply simp
          apply (rule Assume)
          apply simp
         apply (rule Imp_E [where p=\<open>Imp (Imp ?rffa Falsity) ?rfa\<close>])
          apply (rule Imp_I)
          apply (rule Exi_I [where t=\<open>?fa\<close>])
          apply simp
          apply (rule Con_I)
           apply (rule Imp_E [where p=\<open>Imp ?rffa Falsity\<close>])
            apply (rule Assume)
            apply simp
           apply (rule Assume)
           apply simp
          apply (rule Imp_E [where p=\<open>Imp ?rffa Falsity\<close>])
           apply (rule Assume)
           apply simp
          apply (rule Assume)
          apply simp
         apply (rule Imp_E [where p=\<open>Imp (Imp ?rfa Falsity) ?rffa\<close>])
          apply (rule Imp_I)
          apply (rule Imp_I)
          apply (rule Boole)
          apply (rule Imp_E [where p=\<open>?rffa\<close>])
           apply (rule Assume)
           apply simp
          apply (rule Imp_E [where p=\<open>Imp ?rfa Falsity\<close>])
           apply (rule Assume)
           apply simp
          apply (rule Assume)
          apply simp
         apply (rule Assume)
         apply simp
        apply (rule Dis_E [where p=\<open>?rfffa\<close> and q=\<open>Imp ?rfffa Falsity\<close>])
          apply (rule Boole)
          apply (rule Imp_E [where p=\<open>Dis ?rfffa (Imp ?rfffa Falsity)\<close>])
           apply (rule Assume)
           apply simp
          apply (rule Dis_I2)
          apply (rule Imp_I)
          apply (rule Imp_E [where p=\<open>Dis ?rfffa (Imp ?rfffa Falsity)\<close>])
           apply (rule Assume)
           apply simp
          apply (rule Dis_I1)
          apply (rule Assume)
          apply simp
         apply (rule Exi_I [where t=\<open>?fa\<close>])
         apply simp
         apply (rule Con_I)
          apply (rule Imp_E [where p=\<open>Imp ?ra Falsity\<close>])
           apply (rule Assume)
           apply simp
          apply (rule Assume)
          apply simp
         apply (rule Assume)
         apply simp
        apply (rule Imp_E [where p=\<open>Imp (Imp ?rfffa Falsity) ?rffa\<close>])
         apply (rule Imp_I)
         apply (rule Exi_I [where t=\<open>?ffa\<close>])
         apply simp
         apply (rule Con_I)
          apply (rule Imp_E [where p=\<open>Imp ?rfffa Falsity\<close>])
           apply (rule Assume)
           apply simp
          apply (rule Assume)
          apply simp
         apply (rule Imp_E [where p=\<open>Imp ?rfffa Falsity\<close>])
          apply (rule Assume)
          apply simp
         apply (rule Assume)
         apply simp
        apply (rule Imp_E [where p=\<open>Imp (Imp ?rffa Falsity) ?rfffa\<close>])
         apply (rule Imp_I)
         apply (rule Imp_I)
         apply (rule Boole)
         apply (rule Imp_E [where p=\<open>?rfffa\<close>])
          apply (rule Assume)
          apply simp
         apply (rule Imp_E [where p=\<open>Imp ?rffa Falsity\<close>])
          apply (rule Assume)
          apply simp
         apply (rule Assume)
         apply simp
        apply (rule Assume)
        apply simp
       apply (subgoal_tac \<open>OK (sub 0 ?fffa
        (Imp (Imp (Pre ''r'' [Var 0]) Falsity) (Pre ''r'' [Fun ''f'' [Var 0]]))) _\<close>)
        apply simp
       apply (rule Uni_E)
       apply (rule Assume)
       apply simp
      apply (subgoal_tac \<open>OK (sub 0 ?ffa
        (Imp (Imp (Pre ''r'' [Var 0]) Falsity) (Pre ''r'' [Fun ''f'' [Var 0]]))) _\<close>)
       apply simp
      apply (rule Uni_E)
      apply (rule Assume)
      apply simp
     apply (subgoal_tac \<open>OK (sub 0 ?fa
      (Imp (Imp (Pre ''r'' [Var 0]) Falsity) (Pre ''r'' [Fun ''f'' [Var 0]]))) _\<close>)
      apply simp
     apply (rule Uni_E)
     apply (rule Assume)
     apply simp
    apply (subgoal_tac \<open>OK (sub 0 ?a
      (Imp (Imp (Pre ''r'' [Var 0]) Falsity) (Pre ''r'' [Fun ''f'' [Var 0]]))) _\<close>)
     apply simp
    apply (rule Uni_E)
    apply (rule Assume)
    apply simp
    done
qed

lemma open_example: \<open>OK (Dis (Pre ''p'' [Var x]) (Imp Falsity Falsity)) []\<close>
  apply (rule Dis_I2)
  apply (rule Imp_I)
  apply (rule Assume)
  apply simp
  done

section \<open>Soundness\<close>

lemma symbols [simp]:
  \<open>(if p then q else True) = (p \<longrightarrow> q)\<close>
  \<open>(if p then True else q) = (p \<or> q)\<close>
  \<open>(if p then q else False) = (p \<and> q)\<close>
  by simp_all

fun put :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a\<close> where
  \<open>put e v x = (\<lambda>n. if n < v then e n else if n = v then x else e (n - 1))\<close>

lemma \<open>put e 0 x = (\<lambda>n. if n = 0 then x else e (n - 1))\<close>
  by simp

lemma simps [simp]:
  \<open>semantics e f g (Exi p) = (\<exists>x. semantics (put e 0 x) f g p)\<close>
  \<open>semantics e f g (Uni p) = (\<forall>x. semantics (put e 0 x) f g p)\<close>
  by simp_all

lemma increment:
  \<open>semantics_term (put e 0 x) f (inc_term t) = semantics_term e f t\<close>
  \<open>semantics_list (put e 0 x) f (inc_list l) = semantics_list e f l\<close>
  by (induct t and l rule: semantics_term.induct semantics_list.induct) simp_all

lemma commute: \<open>put (put e v x) 0 y = put (put e 0 y) (v + 1) x\<close>
  by fastforce

lemma allnew [simp]: \<open>list_all (new c) z = news c z\<close>
  by (induct z) simp_all

lemma map' [simp]:
  \<open>new_term n t \<Longrightarrow> semantics_term e (f(n := x)) t = semantics_term e f t\<close>
  \<open>new_list n l \<Longrightarrow> semantics_list e (f(n := x)) l = semantics_list e f l\<close>
  by (induct t and l rule: semantics_term.induct semantics_list.induct) auto

lemma map [simp]: \<open>new n p \<Longrightarrow> semantics e (f(n := x)) g p = semantics e f g p\<close>
  by (induct p arbitrary: e) simp_all

lemma allmap' [simp]: \<open>list_all (\<lambda>p. new c p) z \<Longrightarrow>
  list_all (semantics e (f(c := m)) g) z = list_all (semantics e f g) z\<close>
  by (induct z) simp_all

lemma allmap [simp]: \<open>news c z \<Longrightarrow>
  list_all (semantics e (f(c := m)) g) z = list_all (semantics e f g) z\<close>
  by simp

lemma substitute' [simp]:
  \<open>semantics_term e f (sub_term v s t) = semantics_term (put e v (semantics_term e f s)) f t\<close>
  \<open>semantics_list e f (sub_list v s l) = semantics_list (put e v (semantics_term e f s)) f l\<close>
  by (induct t and l rule: semantics_term.induct semantics_list.induct) simp_all

lemma substitute [simp]:
  \<open>semantics e f g (sub v t p) = semantics (put e v (semantics_term e f t)) f g p\<close>
proof (induct p arbitrary: e v t)
  case (Exi p)
  have \<open>semantics e f g (sub v t (Exi p)) =
      (\<exists>x. semantics (put e 0 x) f g (sub (v + 1) (inc_term t) p))\<close>
    by simp
  also have \<open>\<dots> = (\<exists>x. semantics (put (put e 0 x) (v + 1)
      (semantics_term (put e 0 x) f (inc_term t))) f g p)\<close>
    using Exi by simp
  also have \<open>\<dots> = (\<exists>x. semantics (put (put e v (semantics_term e f t)) 0 x) f g p)\<close>
    using commute increment(1) by metis
  finally show ?case
    by simp
next
  case (Uni p)
  have \<open>semantics e f g (sub v t (Uni p)) =
      (\<forall>x. semantics (put e 0 x) f g (sub (v + 1) (inc_term t) p))\<close>
    by simp
  also have \<open>\<dots> =
      (\<forall>x. semantics (put (put e 0 x) (v + 1) (semantics_term (put e 0 x) f (inc_term t))) f g p)\<close>
    using Uni by simp
  also have \<open>\<dots> = (\<forall>x. semantics (put (put e v (semantics_term e f t)) 0 x) f g p)\<close>
    using commute increment(1) by metis
  finally show ?case
    by simp
qed simp_all

lemma member_set [simp]: \<open>p \<in> set z = member p z\<close>
  by (induct z) simp_all

lemma soundness': \<open>OK p z \<Longrightarrow> list_all (semantics e f g) z \<Longrightarrow> semantics e f g p\<close>
proof (induct p z arbitrary: f rule: OK.induct)
  case (Exi_E p z q c)
  then obtain x where \<open>semantics (put e 0 x) f g p\<close>
    by auto
  then have \<open>semantics (put e 0 x) (f(c := \<lambda>w. x)) g p\<close>
    using \<open>news c (p # q # z)\<close> by simp
  then have \<open>semantics e (f(c := \<lambda>w. x)) g (sub 0 (Fun c []) p)\<close>
    by simp
  then have \<open>list_all (semantics e (f(c := \<lambda>w. x)) g) (sub 0 (Fun c []) p # z)\<close>
    using Exi_E by simp
  then have \<open>semantics e (f(c := \<lambda>w. x)) g q\<close>
    using Exi_E by blast
  then show \<open>semantics e f g q\<close>
    using \<open>news c (p # q # z)\<close> by simp
next
  case (Uni_I c p z)
  then have \<open>\<forall>x. list_all (semantics e (f(c := \<lambda>w. x)) g) z\<close>
    by simp
  then have \<open>\<forall>x. semantics e (f(c := \<lambda>w. x)) g (sub 0 (Fun c []) p)\<close>
    using Uni_I by blast
  then have \<open>\<forall>x. semantics (put e 0 x) (f(c := \<lambda>w. x)) g p\<close>
    by simp
  then have \<open>\<forall>x. semantics (put e 0 x) f g p\<close>
    using \<open>news c (p # z)\<close> by simp
  then show \<open>semantics e f g (Uni p)\<close>
    by simp
qed (auto simp: list_all_iff)

theorem soundness: \<open>OK p [] \<Longrightarrow> semantics e f g p\<close>
  by (simp add: soundness')

corollary \<open>\<exists>p. OK p []\<close> \<open>\<exists>p. \<not> OK p []\<close>
proof -
  have \<open>OK (Imp p p) []\<close> for p
    by (rule Imp_I, rule Assume, simp)
  then show \<open>\<exists>p. OK p []\<close>
    by iprover
next
  have \<open>\<not> semantics (e :: nat \<Rightarrow> unit) f g Falsity\<close> for e f g
    by simp
  then show \<open>\<exists>p. \<not> OK p []\<close>
    using soundness by iprover
qed

section \<open>Utilities\<close>

lemma set_inter_compl_diff: \<open>- A \<inter> B = B - A\<close> unfolding Diff_eq using inf_commute .

abbreviation Neg :: \<open>fm \<Rightarrow> fm\<close> where \<open>Neg p \<equiv> Imp p Falsity\<close>

primrec size_formulas :: \<open>fm \<Rightarrow> nat\<close> where
  \<open>size_formulas Falsity = 0\<close> |
  \<open>size_formulas (Pre _ _) = 0\<close> |
  \<open>size_formulas (Con p q) = size_formulas p + size_formulas q + 1\<close> |
  \<open>size_formulas (Dis p q) = size_formulas p + size_formulas q + 1\<close> |
  \<open>size_formulas (Imp p q) = size_formulas p + size_formulas q + 1\<close> |
  \<open>size_formulas (Uni p) = size_formulas p + 1\<close> |
  \<open>size_formulas (Exi p) = size_formulas p + 1\<close>

lemma sub_size_formulas [simp]: \<open>size_formulas (sub i t p) = size_formulas p\<close>
  by (induct p arbitrary: i t) simp_all

subsection \<open>Extra rules\<close>

lemma explosion: \<open>OK (Imp Falsity p) z\<close>
  apply (rule Imp_I) apply (rule Boole) apply (rule Assume) by simp

lemma cut: \<open>OK p z \<Longrightarrow> OK q (p # z) \<Longrightarrow> OK q z\<close>
  apply (rule Imp_E) apply (rule Imp_I) .

lemma Falsity_E: \<open>OK Falsity z \<Longrightarrow> OK p z\<close>
  apply (rule Imp_E) apply (rule explosion) .

lemma Boole': \<open>OK p (Neg p # z) \<Longrightarrow> OK p z\<close>
  apply (rule Boole) apply (rule Imp_E) apply (rule Assume) by simp iprover

subsection \<open>Closed formulas\<close>

primrec
  closed_term :: \<open>nat \<Rightarrow> tm \<Rightarrow> bool\<close> and
  closed_list :: \<open>nat \<Rightarrow> tm list \<Rightarrow> bool\<close> where
  \<open>closed_term m (Var n) = (n < m)\<close> |
  \<open>closed_term m (Fun a ts) = closed_list m ts\<close> |
  \<open>closed_list m [] = True\<close> |
  \<open>closed_list m (t # ts) = (closed_term m t \<and> closed_list m ts)\<close>

primrec closed :: \<open>nat \<Rightarrow> fm \<Rightarrow> bool\<close> where
  \<open>closed m Falsity = True\<close> |
  \<open>closed m (Pre b ts) = closed_list m ts\<close> |
  \<open>closed m (Con p q) = (closed m p \<and> closed m q)\<close> |
  \<open>closed m (Dis p q) = (closed m p \<and> closed m q)\<close> |
  \<open>closed m (Imp p q) = (closed m p \<and> closed m q)\<close> |
  \<open>closed m (Uni p) = closed (Suc m) p\<close> |
  \<open>closed m (Exi p) = closed (Suc m) p\<close>

lemma closed_mono':
  assumes \<open>i \<le> j\<close>
  shows \<open>closed_term i t \<Longrightarrow> closed_term j t\<close>
    and \<open>closed_list i l \<Longrightarrow> closed_list j l\<close>
  using assms by (induct t and l rule: closed_term.induct closed_list.induct) simp_all

lemma closed_mono: \<open>i \<le> j \<Longrightarrow> closed i p \<Longrightarrow> closed j p\<close>
proof (induct p arbitrary: i j)
  case (Pre i l)
  then show ?case
    using closed_mono' by simp
next
  case (Exi p)
  then have \<open>closed (Suc i) p\<close>
    by simp
  then have \<open>closed (Suc j) p\<close>
    using Exi by blast
  then show ?case
    by simp
next
  case (Uni p)
  then have \<open>closed (Suc i) p\<close>
    by simp
  then have \<open>closed (Suc j) p\<close>
    using Uni by blast
  then show ?case
    by simp
qed simp_all

lemma inc_closed [simp]:
  \<open>closed_term 0 t \<Longrightarrow> closed_term 0 (inc_term t)\<close>
  \<open>closed_list 0 l \<Longrightarrow> closed_list 0 (inc_list l)\<close>
  by (induct t and l rule: closed_term.induct closed_list.induct) simp_all

lemma sub_closed' [simp]:
  assumes \<open>closed_term 0 u\<close>
  shows \<open>closed_term (Suc i) t \<Longrightarrow> closed_term i (sub_term i u t)\<close>
    and \<open>closed_list (Suc i) l \<Longrightarrow> closed_list i (sub_list i u l)\<close>
  using assms
proof (induct t and l rule: closed_term.induct closed_list.induct)
  case (Var x)
  then show ?case
    using closed_mono'(1) by auto
qed simp_all

lemma sub_closed [simp]: \<open>closed_term 0 t \<Longrightarrow> closed (Suc i) p \<Longrightarrow> closed i (sub i t p)\<close>
  by (induct p arbitrary: i t) simp_all

subsection \<open>Parameters\<close>

primrec
  params_term :: \<open>tm \<Rightarrow> id set\<close> and
  params_list :: \<open>tm list \<Rightarrow> id set\<close> where
  \<open>params_term (Var n) = {}\<close> |
  \<open>params_term (Fun a ts) = {a} \<union> params_list ts\<close> |
  \<open>params_list [] = {}\<close> |
  \<open>params_list (t # ts) = (params_term t \<union> params_list ts)\<close>

primrec params :: \<open>fm \<Rightarrow> id set\<close> where
  \<open>params Falsity = {}\<close> |
  \<open>params (Pre b ts) = params_list ts\<close> |
  \<open>params (Con p q) = params p \<union> params q\<close> |
  \<open>params (Dis p q) = params p \<union> params q\<close> |
  \<open>params (Imp p q) = params p \<union> params q\<close> |
  \<open>params (Uni p) = params p\<close> |
  \<open>params (Exi p) = params p\<close>

lemma new_params' [simp]:
  \<open>new_term c t = (c \<notin> params_term t)\<close>
  \<open>new_list c l = (c \<notin> params_list l)\<close>
  by (induct t and l rule: new_term.induct new_list.induct) simp_all

lemma new_params [simp]: \<open>new x p = (x \<notin> params p)\<close>
  by (induct p) simp_all

lemma news_params [simp]: \<open>news c z = list_all (\<lambda>p. c \<notin> params p) z\<close>
  by (induct z) simp_all

lemma params_inc [simp]:
  \<open>params_term (inc_term t) = params_term t\<close>
  \<open>params_list (inc_list l) = params_list l\<close>
  by (induct t and l rule: sub_term.induct sub_list.induct) simp_all

primrec
  psubst_term :: \<open>(id \<Rightarrow> id) \<Rightarrow> tm \<Rightarrow> tm\<close> and
  psubst_list :: \<open>(id \<Rightarrow> id) \<Rightarrow> tm list \<Rightarrow> tm list\<close> where
  \<open>psubst_term f (Var i) = Var i\<close> |
  \<open>psubst_term f (Fun x ts) = Fun (f x) (psubst_list f ts)\<close> |
  \<open>psubst_list f [] = []\<close> |
  \<open>psubst_list f (t # ts) = psubst_term f t # psubst_list f ts\<close>

primrec psubst :: \<open>(id \<Rightarrow> id) \<Rightarrow> fm \<Rightarrow> fm\<close> where
  \<open>psubst f Falsity = Falsity\<close> |
  \<open>psubst f (Pre b ts) = Pre b (psubst_list f ts)\<close> |
  \<open>psubst f (Con p q) = Con (psubst f p) (psubst f q)\<close> |
  \<open>psubst f (Dis p q) = Dis (psubst f p) (psubst f q)\<close> |
  \<open>psubst f (Imp p q) = Imp (psubst f p) (psubst f q)\<close> |
  \<open>psubst f (Uni p) = Uni (psubst f p)\<close> |
  \<open>psubst f (Exi p) = Exi (psubst f p)\<close>

lemma psubst_closed' [simp]:
  \<open>closed_term i (psubst_term f t) = closed_term i t\<close>
  \<open>closed_list i (psubst_list f l) = closed_list i l\<close>
  by (induct t and l rule: closed_term.induct closed_list.induct) simp_all

lemma psubst_closed [simp]: \<open>closed i (psubst f p) = closed i p\<close>
  by (induct p arbitrary: i) simp_all

lemma psubst_inc [simp]:
  \<open>psubst_term f (inc_term t) = inc_term (psubst_term f t)\<close>
  \<open>psubst_list f (inc_list l) = inc_list (psubst_list f l)\<close>
  by (induct t and l rule: psubst_term.induct psubst_list.induct) simp_all

lemma psubst_sub' [simp]:
  \<open>psubst_term f (sub_term i u t) = sub_term i (psubst_term f u) (psubst_term f t)\<close>
  \<open>psubst_list f (sub_list i u l) = sub_list i (psubst_term f u) (psubst_list f l)\<close>
  by (induct t and l rule: psubst_term.induct psubst_list.induct) simp_all

lemma psubst_sub [simp]: \<open>psubst f (sub i t P) = sub i (psubst_term f t) (psubst f P)\<close>
  by (induct P arbitrary: i t) simp_all

lemma psubst_upd' [simp]:
  \<open>x \<notin> params_term t \<Longrightarrow> psubst_term (f(x := y)) t = psubst_term f t\<close>
  \<open>x \<notin> params_list l \<Longrightarrow> psubst_list (f(x := y)) l = psubst_list f l\<close>
  by (induct t and l rule: psubst_term.induct psubst_list.induct) auto

lemma psubst_upd [simp]: \<open>x \<notin> params P \<Longrightarrow> psubst (f(x := y)) P = psubst f P\<close>
  by (induct P) simp_all

lemma psubst_id': \<open>psubst_term id t = t\<close> \<open>psubst_list (\<lambda>x. x) l = l\<close>
  by (induct t and l rule: psubst_term.induct psubst_list.induct) simp_all

lemma psubst_id [simp]: \<open>psubst id = id\<close>
proof
  fix p
  show \<open>psubst id p = id p\<close>
    by (induct p) (simp_all add: psubst_id')
qed

lemma psubst_image' [simp]:
  \<open>params_term (psubst_term f t) = f ` params_term t\<close>
  \<open>params_list (psubst_list f l) = f ` params_list l\<close>
  by (induct t and l rule: params_term.induct params_list.induct) (simp_all add: image_Un)

lemma psubst_image [simp]: \<open>params (psubst f p) = f ` params p\<close>
  by (induct p) (simp_all add: image_Un)

lemma psubst_semantics' [simp]:
  \<open>semantics_term e f (psubst_term h t) = semantics_term e (\<lambda>x. f (h x)) t\<close>
  \<open>semantics_list e f (psubst_list h l) = semantics_list e (\<lambda>x. f (h x)) l\<close>
  by (induct t and l rule: semantics_term.induct semantics_list.induct) simp_all

lemma psubst_semantics: \<open>semantics e f g (psubst h p) = semantics e (\<lambda>x. f (h x)) g p\<close>
  by (induct p arbitrary: e) simp_all

section \<open>Completeness\<close>

subsection \<open>Consistent sets\<close>

definition consistency :: \<open>fm set set \<Rightarrow> bool\<close> where
  \<open>consistency C = (\<forall>S. S \<in> C \<longrightarrow>
    (\<forall>p ts. \<not> (Pre p ts \<in> S \<and> Neg (Pre p ts) \<in> S)) \<and>
    Falsity \<notin> S \<and>
    (\<forall>Z. Neg (Neg Z) \<in> S \<longrightarrow> S \<union> {Z} \<in> C) \<and>
    (\<forall>A B. Con A B \<in> S \<longrightarrow> S \<union> {A, B} \<in> C) \<and>
    (\<forall>A B. Neg (Dis A B) \<in> S \<longrightarrow> S \<union> {Neg A, Neg B} \<in> C) \<and>
    (\<forall>A B. Dis A B \<in> S \<longrightarrow> S \<union> {A} \<in> C \<or> S \<union> {B} \<in> C) \<and>
    (\<forall>A B. Neg (Con A B) \<in> S \<longrightarrow> S \<union> {Neg A} \<in> C \<or> S \<union> {Neg B} \<in> C) \<and>
    (\<forall>A B. Imp A B \<in> S \<longrightarrow> S \<union> {Neg A} \<in> C \<or> S \<union> {B} \<in> C) \<and>
    (\<forall>A B. Neg (Imp A B) \<in> S \<longrightarrow> S \<union> {A, Neg B} \<in> C) \<and>
    (\<forall>P t. closed_term 0 t \<longrightarrow> Uni P \<in> S \<longrightarrow> S \<union> {sub 0 t P} \<in> C) \<and>
    (\<forall>P t. closed_term 0 t \<longrightarrow> Neg (Exi P) \<in> S \<longrightarrow> S \<union> {Neg (sub 0 t P)} \<in> C) \<and>
    (\<forall>P. Exi P \<in> S \<longrightarrow> (\<exists>x. S \<union> {sub 0 (Fun x []) P} \<in> C)) \<and>
    (\<forall>P. Neg (Uni P) \<in> S \<longrightarrow> (\<exists>x. S \<union> {Neg (sub 0 (Fun x []) P)} \<in> C)))\<close>

definition alt_consistency :: \<open>fm set set \<Rightarrow> bool\<close> where
  \<open>alt_consistency C = (\<forall>S. S \<in> C \<longrightarrow>
     (\<forall>p ts. \<not> (Pre p ts \<in> S \<and> Neg (Pre p ts) \<in> S)) \<and>
     Falsity \<notin> S \<and>
     (\<forall>Z. Neg (Neg Z) \<in> S \<longrightarrow> S \<union> {Z} \<in> C) \<and>
     (\<forall>A B. Con A B \<in> S \<longrightarrow> S \<union> {A, B} \<in> C) \<and>
     (\<forall>A B. Neg (Dis A B) \<in> S \<longrightarrow> S \<union> {Neg A, Neg B} \<in> C) \<and>
     (\<forall>A B. Dis A B \<in> S \<longrightarrow> S \<union> {A} \<in> C \<or> S \<union> {B} \<in> C) \<and>
     (\<forall>A B. Neg (Con A B) \<in> S \<longrightarrow> S \<union> {Neg A} \<in> C \<or> S \<union> {Neg B} \<in> C) \<and>
     (\<forall>A B. Imp A B \<in> S \<longrightarrow> S \<union> {Neg A} \<in> C \<or> S \<union> {B} \<in> C) \<and>
     (\<forall>A B. Neg (Imp A B) \<in> S \<longrightarrow> S \<union> {A, Neg B} \<in> C) \<and>
     (\<forall>P t. closed_term 0 t \<longrightarrow> Uni P \<in> S \<longrightarrow> S \<union> {sub 0 t P} \<in> C) \<and>
     (\<forall>P t. closed_term 0 t \<longrightarrow> Neg (Exi P) \<in> S \<longrightarrow> S \<union> {Neg (sub 0 t P)} \<in> C) \<and>
     (\<forall>P x. (\<forall>a \<in> S. x \<notin> params a) \<longrightarrow> Exi P \<in> S \<longrightarrow> S \<union> {sub 0 (Fun x []) P} \<in> C) \<and>
     (\<forall>P x. (\<forall>a \<in> S. x \<notin> params a) \<longrightarrow> Neg (Uni P) \<in> S \<longrightarrow> S \<union> {Neg (sub 0 (Fun x []) P)} \<in> C))\<close>

definition mk_alt_consistency :: \<open>fm set set \<Rightarrow> fm set set\<close> where
  \<open>mk_alt_consistency C = {S. \<exists>f. psubst f ` S \<in> C}\<close>

theorem alt_consistency:
  assumes conc: \<open>consistency C\<close>
  shows \<open>alt_consistency (mk_alt_consistency C)\<close> (is \<open>alt_consistency ?C'\<close>)
  unfolding alt_consistency_def
proof (intro allI impI conjI)
  fix S'

  assume \<open>S' \<in> ?C'\<close>
  then obtain f where sc: \<open>psubst f ` S' \<in> C\<close> (is \<open>?S \<in> C\<close>)
    unfolding mk_alt_consistency_def by blast

  fix p ts
  show \<open>\<not> (Pre p ts \<in> S' \<and> Neg (Pre p ts) \<in> S')\<close>
  proof
    assume *: \<open>Pre p ts \<in> S' \<and> Neg (Pre p ts) \<in> S'\<close>
    then have \<open>psubst f (Pre p ts) \<in> ?S\<close>
      by blast
    then have \<open>Pre p (psubst_list f ts) \<in> ?S\<close>
      by simp
    then have \<open>Neg (Pre p (psubst_list f ts)) \<notin> ?S\<close>
      using conc sc by (simp add: consistency_def)
    then have \<open>Neg (Pre p ts) \<notin> S'\<close>
      by force
    then show False
      using * by blast
  qed

  have \<open>Falsity \<notin> ?S\<close>
    using conc sc unfolding consistency_def by simp
  then show \<open>Falsity \<notin> S'\<close>
    by force

  { fix Z
    assume \<open>Neg (Neg Z) \<in> S'\<close>
    then have \<open>psubst f (Neg (Neg Z)) \<in> ?S\<close>
      by blast
    then have \<open>?S \<union> {psubst f Z} \<in> C\<close>
      using conc sc by (simp add: consistency_def)
    then show \<open>S' \<union> {Z} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by auto }

  { fix A B
    assume \<open>Con A B \<in> S'\<close>
    then have \<open>psubst f (Con A B) \<in> ?S\<close>
      by blast
    then have \<open>?S \<union> {psubst f A, psubst f B} \<in> C\<close>
      using conc sc by (simp add: consistency_def)
    then show \<open>S' \<union> {A, B} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by auto }

  { fix A B
    assume \<open>Neg (Dis A B) \<in> S'\<close>
    then have \<open>psubst f (Neg (Dis A B)) \<in> ?S\<close>
      by blast
    then have \<open>?S \<union> {Neg (psubst f A), Neg (psubst f B)} \<in> C\<close>
      using conc sc by (simp add: consistency_def)
    then show \<open>S' \<union> {Neg A, Neg B} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by auto }

  { fix A B
    assume \<open>Neg (Imp A B) \<in> S'\<close>
    then have \<open>psubst f (Neg (Imp A B)) \<in> ?S\<close>
      by blast
    then have \<open>?S \<union> {psubst f A, Neg (psubst f B)} \<in> C\<close>
      using conc sc by (simp add: consistency_def)
    then show \<open>S' \<union> {A, Neg B} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by auto }

  { fix A B
    assume \<open>Dis A B \<in> S'\<close>
    then have \<open>psubst f (Dis A B) \<in> ?S\<close>
      by blast
    then have \<open>?S \<union> {psubst f A} \<in> C \<or> ?S \<union> {psubst f B} \<in> C\<close>
      using conc sc by (simp add: consistency_def)
    then show \<open>S' \<union> {A} \<in> ?C' \<or> S' \<union> {B} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by auto }

  { fix A B
    assume \<open>Neg (Con A B) \<in> S'\<close>
    then have \<open>psubst f (Neg (Con A B)) \<in> ?S\<close>
      by blast
    then have \<open>?S \<union> {Neg (psubst f A)} \<in> C \<or> ?S \<union> {Neg (psubst f B)} \<in> C\<close>
      using conc sc by (simp add: consistency_def)
    then show \<open>S' \<union> {Neg A} \<in> ?C' \<or> S' \<union> {Neg B} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by auto }

  { fix A B
    assume \<open>Imp A B \<in> S'\<close>
    then have \<open>psubst f (Imp A B) \<in> ?S\<close>
      by blast
    then have \<open>?S \<union> {Neg (psubst f A)} \<in> C \<or> ?S \<union> {psubst f B} \<in> C\<close>
      using conc sc by (simp add: consistency_def)
    then show \<open>S' \<union> {Neg A} \<in> ?C' \<or> S' \<union> {B} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by auto }

  { fix P t
    assume \<open>closed_term 0 t\<close> and \<open>Uni P \<in> S'\<close>
    then have \<open>psubst f (Uni P) \<in> ?S\<close>
      by blast
    then have \<open>?S \<union> {sub 0 (psubst_term f t) (psubst f P)} \<in> C\<close>
      using \<open>closed_term 0 t\<close> conc sc by (simp add: consistency_def)
    then show \<open>S' \<union> {sub 0 t P} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by auto }

  { fix P t
    assume \<open>closed_term 0 t\<close> and \<open>Neg (Exi P) \<in> S'\<close>
    then have \<open>psubst f (Neg (Exi P)) \<in> ?S\<close>
      by blast
    then have \<open>?S \<union> {Neg (sub 0 (psubst_term f t) (psubst f P))} \<in> C\<close>
      using \<open>closed_term 0 t\<close> conc sc by (simp add: consistency_def)
    then show \<open>S' \<union> {Neg (sub 0 t P)} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by auto }

  { fix P x
    assume \<open>\<forall>a \<in> S'. x \<notin> params a\<close> and \<open>Exi P \<in> S'\<close>
    moreover have \<open>psubst f (Exi P) \<in> ?S\<close>
      using calculation by blast
    then have \<open>\<exists>y. ?S \<union> {sub 0 (Fun y []) (psubst f P)} \<in> C\<close>
      using conc sc by (simp add: consistency_def)
    then obtain y where \<open>?S \<union> {sub 0 (Fun y []) (psubst f P)} \<in> C\<close>
      by blast

    moreover have \<open>psubst (f(x := y)) ` S' = ?S\<close>
      using calculation by (simp cong add: image_cong)
    then have \<open>psubst (f(x := y)) `
        S' \<union> {sub 0 (Fun ((f(x := y)) x) []) (psubst (f(x := y)) P)} \<in> C\<close>
      using calculation by auto
    then have \<open>\<exists>f. psubst f `
        S' \<union> {sub 0 (Fun (f x) []) (psubst f P)} \<in> C\<close>
      by blast
    then show \<open>S' \<union> {sub 0 (Fun x []) P} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by simp }

  { fix P x
    assume \<open>\<forall>a \<in> S'. x \<notin> params a\<close> and \<open>Neg (Uni P) \<in> S'\<close>
    moreover have \<open>psubst f (Neg (Uni P)) \<in> ?S\<close>
      using calculation by blast
    then have \<open>\<exists>y. ?S \<union> {Neg (sub 0 (Fun y []) (psubst f P))} \<in> C\<close>
      using conc sc by (simp add: consistency_def)
    then obtain y where \<open>?S \<union> {Neg (sub 0 (Fun y []) (psubst f P))} \<in> C\<close>
      by blast

    moreover have \<open>psubst (f(x := y)) ` S' = ?S\<close>
      using calculation by (simp cong add: image_cong)
    moreover have \<open>psubst (f(x := y)) `
    S' \<union> {Neg (sub 0 (Fun ((f(x := y)) x) []) (psubst (f(x := y)) P))} \<in> C\<close>
      using calculation by auto
    ultimately have \<open>\<exists>f. psubst f ` S' \<union> {Neg (sub 0 (Fun (f x) []) (psubst f P))} \<in> C\<close>
      by blast
    then show \<open>S' \<union> {Neg (sub 0 (Fun x []) P)} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by simp }
qed

theorem mk_alt_consistency_subset: \<open>C \<subseteq> mk_alt_consistency C\<close>
  unfolding mk_alt_consistency_def
proof
  fix S
  assume \<open>S \<in> C\<close>
  then have \<open>psubst id ` S \<in> C\<close>
    by simp
  then have \<open>\<exists>f. psubst f ` S \<in> C\<close>
    by blast
  then show \<open>S \<in> {S. \<exists>f. psubst f ` S \<in> C}\<close>
    by simp
qed

subsection \<open>Closure under subsets\<close>

definition close :: \<open>fm set set \<Rightarrow> fm set set\<close> where
  \<open>close C = {S. \<exists>S' \<in> C. S \<subseteq> S'}\<close>

definition subset_closed :: \<open>'a set set \<Rightarrow> bool\<close> where
  \<open>subset_closed C = (\<forall>S' \<in> C. \<forall>S. S \<subseteq> S' \<longrightarrow> S \<in> C)\<close>

lemma subset_in_close:
  assumes \<open>S' \<subseteq> S\<close> and \<open>S \<union> x \<in> C\<close>
  shows \<open>S' \<union> x \<in> close C\<close>
proof -
  have \<open>S \<union> x \<in> close C\<close>
    unfolding close_def using \<open>S \<union> x \<in> C\<close> by blast
  then show ?thesis
    unfolding close_def using \<open>S' \<subseteq> S\<close> by blast
qed

theorem close_consistency:
  assumes conc: \<open>consistency C\<close>
  shows \<open>consistency (close C)\<close>
  unfolding consistency_def
proof (intro allI impI conjI)
  fix S'
  assume \<open>S' \<in> close C\<close>
  then obtain S where \<open>S \<in> C\<close> and \<open>S' \<subseteq> S\<close>
    unfolding close_def by blast

  { fix p ts
    have \<open>\<not> (Pre p ts \<in> S \<and> Neg (Pre p ts) \<in> S)\<close>
      using \<open>S \<in> C\<close> conc unfolding consistency_def by simp
    then show \<open>\<not> (Pre p ts \<in> S' \<and> Neg (Pre p ts) \<in> S')\<close>
      using \<open>S' \<subseteq> S\<close> by blast }

  { have \<open>Falsity \<notin> S\<close>
      using \<open>S \<in> C\<close> conc unfolding consistency_def by blast
    then show \<open>Falsity \<notin> S'\<close>
      using \<open>S' \<subseteq> S\<close> by blast }

  { fix Z
    assume \<open>Neg (Neg Z) \<in> S'\<close>
    then have \<open>Neg (Neg Z) \<in> S\<close>
      using \<open>S' \<subseteq> S\<close> by blast
    then have \<open>S \<union> {Z} \<in> C\<close>
      using \<open>S \<in> C\<close> conc unfolding consistency_def by simp
    then show \<open>S' \<union> {Z} \<in> close C\<close>
      using \<open>S' \<subseteq> S\<close> subset_in_close by blast }

  { fix A B
    assume \<open>Con A B \<in> S'\<close>
    then have \<open>Con A B \<in> S\<close>
      using \<open>S' \<subseteq> S\<close> by blast
    then have \<open>S \<union> {A, B} \<in> C\<close>
      using \<open>S \<in> C\<close> conc unfolding consistency_def by simp
    then show \<open>S' \<union> {A, B} \<in> close C\<close>
      using \<open>S' \<subseteq> S\<close> subset_in_close by blast }

  { fix A B
    assume \<open>Neg (Dis A B) \<in> S'\<close>
    then have \<open>Neg (Dis A B) \<in> S\<close>
      using \<open>S' \<subseteq> S\<close> by blast
    then have \<open>S \<union> {Neg A, Neg B} \<in> C\<close>
      using \<open>S \<in> C\<close> conc unfolding consistency_def by simp
    then show \<open>S' \<union> {Neg A, Neg B} \<in> close C\<close>
      using \<open>S' \<subseteq> S\<close> subset_in_close by blast }

  { fix A B
    assume \<open>Neg (Imp A B) \<in> S'\<close>
    then have \<open>Neg (Imp A B) \<in> S\<close>
      using \<open>S' \<subseteq> S\<close> by blast
    then have \<open>S \<union> {A, Neg B} \<in> C\<close>
      using \<open>S \<in> C\<close> conc unfolding consistency_def by blast
    then show \<open>S' \<union> {A, Neg B} \<in> close C\<close>
      using \<open>S' \<subseteq> S\<close> subset_in_close by blast }

  { fix A B
    assume \<open>Dis A B \<in> S'\<close>
    then have \<open>Dis A B \<in> S\<close>
      using \<open>S' \<subseteq> S\<close> by blast
    then have \<open>S \<union> {A} \<in> C \<or> S \<union> {B} \<in> C\<close>
      using \<open>S \<in> C\<close> conc unfolding consistency_def by simp
    then show \<open>S' \<union> {A} \<in> close C \<or> S' \<union> {B} \<in> close C\<close>
      using \<open>S' \<subseteq> S\<close> subset_in_close by blast }

  { fix A B
    assume \<open>Neg (Con A B) \<in> S'\<close>
    then have \<open>Neg (Con A B) \<in> S\<close>
      using \<open>S' \<subseteq> S\<close> by blast
    then have \<open>S \<union> {Neg A} \<in> C \<or> S \<union> {Neg B} \<in> C\<close>
      using \<open>S \<in> C\<close> conc unfolding consistency_def by simp
    then show \<open>S' \<union> {Neg A} \<in> close C \<or> S' \<union> {Neg B} \<in> close C\<close>
      using \<open>S' \<subseteq> S\<close> subset_in_close by blast }

  { fix A B
    assume \<open>Imp A B \<in> S'\<close>
    then have \<open>Imp A B \<in> S\<close>
      using \<open>S' \<subseteq> S\<close> by blast
    then have \<open>S \<union> {Neg A} \<in> C \<or> S \<union> {B} \<in> C\<close>
      using \<open>S \<in> C\<close> conc unfolding consistency_def by simp
    then show \<open>S' \<union> {Neg A} \<in> close C \<or> S' \<union> {B} \<in> close C\<close>
      using \<open>S' \<subseteq> S\<close> subset_in_close by blast }

  { fix P t
    assume \<open>closed_term 0 t\<close> and \<open>Uni P \<in> S'\<close>
    then have \<open>Uni P \<in> S\<close>
      using \<open>S' \<subseteq> S\<close> by blast
    then have \<open>S \<union> {sub 0 t P} \<in> C\<close>
      using \<open>closed_term 0 t\<close> \<open>S \<in> C\<close> conc
      unfolding consistency_def by blast
    then show \<open>S' \<union> {sub 0 t P} \<in> close C\<close>
      using \<open>S' \<subseteq> S\<close> subset_in_close by blast }

  { fix P t
    assume \<open>closed_term 0 t\<close> and \<open>Neg (Exi P) \<in> S'\<close>
    then have \<open>Neg (Exi P) \<in> S\<close>
      using \<open>S' \<subseteq> S\<close> by blast
    then have \<open>S \<union> {Neg (sub 0 t P)} \<in> C\<close>
      using \<open>closed_term 0 t\<close> \<open>S \<in> C\<close> conc
      unfolding consistency_def by blast
    then show \<open>S' \<union> {Neg (sub 0 t P)} \<in> close C\<close>
      using \<open>S' \<subseteq> S\<close> subset_in_close by blast }

  { fix P
    assume \<open>Exi P \<in> S'\<close>
    then have \<open>Exi P \<in> S\<close>
      using \<open>S' \<subseteq> S\<close> by blast
    then have \<open>\<exists>c. S \<union> {sub 0 (Fun c []) P} \<in> C\<close>
      using \<open>S \<in> C\<close> conc unfolding consistency_def by blast
    then show \<open>\<exists>c. S' \<union> {sub 0 (Fun c []) P} \<in> close C\<close>
      using \<open>S' \<subseteq> S\<close> subset_in_close by blast }

  { fix P
    assume \<open>Neg (Uni P) \<in> S'\<close>
    then have \<open>Neg (Uni P) \<in> S\<close>
      using \<open>S' \<subseteq> S\<close> by blast
    then have \<open>\<exists>c. S \<union> {Neg (sub 0 (Fun c []) P)} \<in> C\<close>
      using \<open>S \<in> C\<close> conc unfolding consistency_def by simp
    then show \<open>\<exists>c. S' \<union> {Neg (sub 0 (Fun c []) P)} \<in> close C\<close>
      using \<open>S' \<subseteq> S\<close> subset_in_close by blast }
qed

theorem close_closed: \<open>subset_closed (close C)\<close>
  unfolding close_def subset_closed_def by blast

theorem close_subset: \<open>C \<subseteq> close C\<close>
  unfolding close_def by blast

theorem mk_alt_consistency_closed:
  assumes \<open>subset_closed C\<close>
  shows \<open>subset_closed (mk_alt_consistency C)\<close>
  unfolding subset_closed_def
proof (intro ballI allI impI)
  fix S S'
  assume \<open>S \<in> mk_alt_consistency C\<close> and \<open>S' \<subseteq> S\<close>
  then obtain f where *: \<open>psubst f ` S \<in> C\<close>
    unfolding mk_alt_consistency_def by blast
  moreover have \<open>psubst f ` S' \<subseteq> psubst f ` S\<close>
    using \<open>S' \<subseteq> S\<close> by blast
  ultimately have \<open>psubst f ` S' \<in> C\<close>
    using \<open>subset_closed C\<close> unfolding subset_closed_def by blast
  then show \<open>S' \<in> mk_alt_consistency C\<close>
    unfolding mk_alt_consistency_def by blast
qed

subsection \<open>Finite character\<close>

definition finite_char :: \<open>'a set set \<Rightarrow> bool\<close> where
  \<open>finite_char C = (\<forall>S. S \<in> C = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> C))\<close>

definition mk_finite_char :: \<open>'a set set \<Rightarrow> 'a set set\<close> where
  \<open>mk_finite_char C = {S. \<forall>S'. S' \<subseteq> S \<longrightarrow> finite S' \<longrightarrow> S' \<in> C}\<close>

theorem finite_char: \<open>finite_char (mk_finite_char C)\<close>
  unfolding finite_char_def mk_finite_char_def by blast

theorem finite_alt_consistency:
  assumes altconc: \<open>alt_consistency C\<close>
    and \<open>subset_closed C\<close>
  shows \<open>alt_consistency (mk_finite_char C)\<close>
  unfolding alt_consistency_def
proof (intro allI impI conjI)
  fix S
  assume \<open>S \<in> mk_finite_char C\<close>
  then have finc: \<open>\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C\<close>
    unfolding mk_finite_char_def by blast

  have \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
    using \<open>subset_closed C\<close> unfolding subset_closed_def by blast
  then have sc: \<open>\<forall>S' x. S' \<union> x \<in> C \<longrightarrow> (\<forall>S \<subseteq> S' \<union> x. S \<in> C)\<close>
    by blast

  { fix p ts
    show \<open>\<not> (Pre p ts \<in> S \<and> Neg (Pre p ts) \<in> S)\<close>
    proof
      assume \<open>Pre p ts \<in> S \<and> Neg (Pre p ts) \<in> S\<close>
      then have \<open>{Pre p ts, Neg (Pre p ts)} \<in> C\<close>
        using finc by simp
      then show False
        using altconc unfolding alt_consistency_def by fast
    qed }

  show \<open>Falsity \<notin> S\<close>
  proof
    assume \<open>Falsity \<in> S\<close>
    then have \<open>{Falsity} \<in> C\<close>
      using finc by simp
    then show False
      using altconc unfolding alt_consistency_def by fast
  qed

  { fix Z
    assume *: \<open>Neg (Neg Z) \<in> S\<close>
    show \<open>S \<union> {Z} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {Z} \<union> {Neg (Neg Z)}\<close>

      assume \<open>S' \<subseteq> S \<union> {Z}\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {Z} \<in> C\<close>
        using altconc unfolding alt_consistency_def by simp
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }

  { fix A B
    assume *: \<open>Con A B \<in> S\<close>
    show \<open>S \<union> {A, B} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {A, B} \<union> {Con A B}\<close>

      assume \<open>S' \<subseteq> S \<union> {A, B}\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {A, B} \<in> C\<close>
        using altconc unfolding alt_consistency_def by simp
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }

  { fix A B
    assume *: \<open>Neg (Dis A B) \<in> S\<close>
    show \<open>S \<union> {Neg A, Neg B} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {Neg A, Neg B} \<union> {Neg (Dis A B)}\<close>

      assume \<open>S' \<subseteq> S \<union> {Neg A, Neg B}\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {Neg A, Neg B} \<in> C\<close>
        using altconc unfolding alt_consistency_def by simp
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }

  { fix A B
    assume *: \<open>Neg (Imp A B) \<in> S\<close>
    show \<open>S \<union> {A, Neg B} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {A, Neg B} \<union> {Neg (Imp A B)}\<close>

      assume \<open>S' \<subseteq> S \<union> {A, Neg B}\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {A, Neg B} \<in> C\<close>
        using altconc unfolding alt_consistency_def by simp
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }

  { fix A B
    assume *: \<open>Dis A B \<in> S\<close>
    show \<open>S \<union> {A} \<in> mk_finite_char C \<or> S \<union> {B} \<in> mk_finite_char C\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain Sa and Sb
        where \<open>Sa \<subseteq> S \<union> {A}\<close> and \<open>finite Sa\<close> and \<open>Sa \<notin> C\<close>
          and \<open>Sb \<subseteq> S \<union> {B}\<close> and \<open>finite Sb\<close> and \<open>Sb \<notin> C\<close>
        unfolding mk_finite_char_def by blast

      let ?S' = \<open>(Sa - {A}) \<union> (Sb - {B}) \<union> {Dis A B}\<close>

      have \<open>?S' \<subseteq> S\<close>
        using \<open>Sa \<subseteq> S \<union> {A}\<close> \<open>Sb \<subseteq> S \<union> {B}\<close> * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite Sa\<close> \<open>finite Sb\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {A} \<in> C \<or> ?S' \<union> {B} \<in> C\<close>
        using altconc unfolding alt_consistency_def by simp
      then have \<open>Sa \<in> C \<or> Sb \<in> C\<close>
        using sc by blast
      then show False
        using \<open>Sa \<notin> C\<close> \<open>Sb \<notin> C\<close> by blast
    qed }

  { fix A B
    assume *: \<open>Neg (Con A B) \<in> S\<close>
    show \<open>S \<union> {Neg A} \<in> mk_finite_char C \<or> S \<union> {Neg B} \<in> mk_finite_char C\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain Sa and Sb
        where \<open>Sa \<subseteq> S \<union> {Neg A}\<close> and \<open>finite Sa\<close> and \<open>Sa \<notin> C\<close>
          and \<open>Sb \<subseteq> S \<union> {Neg B}\<close> and \<open>finite Sb\<close> and \<open>Sb \<notin> C\<close>
        unfolding mk_finite_char_def by blast

      let ?S' = \<open>(Sa - {Neg A}) \<union> (Sb - {Neg B}) \<union> {Neg (Con A B)}\<close>

      have \<open>?S' \<subseteq> S\<close>
        using \<open>Sa \<subseteq> S \<union> {Neg A}\<close> \<open>Sb \<subseteq> S \<union> {Neg B}\<close> * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite Sa\<close> \<open>finite Sb\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {Neg A} \<in> C \<or> ?S' \<union> {Neg B} \<in> C\<close>
        using altconc unfolding alt_consistency_def by simp
      then have \<open>Sa \<in> C \<or> Sb \<in> C\<close>
        using sc by blast
      then show False
        using \<open>Sa \<notin> C\<close> \<open>Sb \<notin> C\<close> by blast
    qed }

  { fix A B
    assume *: \<open>Imp A B \<in> S\<close>
    show \<open>S \<union> {Neg A} \<in> mk_finite_char C \<or> S \<union> {B} \<in> mk_finite_char C\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain Sa and Sb
        where \<open>Sa \<subseteq> S \<union> {Neg A}\<close> and \<open>finite Sa\<close> and \<open>Sa \<notin> C\<close>
          and \<open>Sb \<subseteq> S \<union> {B}\<close> and \<open>finite Sb\<close> and \<open>Sb \<notin> C\<close>
        unfolding mk_finite_char_def by blast

      let ?S' = \<open>(Sa - {Neg A}) \<union> (Sb - {B}) \<union> {Imp A B}\<close>

      have \<open>?S' \<subseteq> S\<close>
        using \<open>Sa \<subseteq> S \<union> {Neg A}\<close> \<open>Sb \<subseteq> S \<union> {B}\<close> * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite Sa\<close> \<open>finite Sb\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {Neg A} \<in> C \<or> ?S' \<union> {B} \<in> C\<close>
        using altconc unfolding alt_consistency_def by simp
      then have \<open>Sa \<in> C \<or> Sb \<in> C\<close>
        using sc by blast
      then show False
        using \<open>Sa \<notin> C\<close> \<open>Sb \<notin> C\<close> by blast
    qed }

  { fix P t
    assume *: \<open>Uni P \<in> S\<close> and \<open>closed_term 0 t\<close>
    show \<open>S \<union> {sub 0 t P} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {sub 0 t P} \<union> {Uni P}\<close>

      assume \<open>S' \<subseteq> S \<union> {sub 0 t P}\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {sub 0 t P} \<in> C\<close>
        using altconc \<open>closed_term 0 t\<close>
        unfolding alt_consistency_def by simp
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }

  { fix P t
    assume *: \<open>Neg (Exi P) \<in> S\<close> and \<open>closed_term 0 t\<close>
    show \<open>S \<union> {Neg (sub 0 t P)} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {Neg (sub 0 t P)} \<union> {Neg (Exi P)}\<close>

      assume \<open>S' \<subseteq> S \<union> {Neg (sub 0 t P)}\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {Neg (sub 0 t P)} \<in> C\<close>
        using altconc \<open>closed_term 0 t\<close>
        unfolding alt_consistency_def by simp
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }

  { fix P x
    assume *: \<open>Exi P \<in> S\<close> and \<open>\<forall>a \<in> S. x \<notin> params a\<close>
    show \<open>S \<union> {sub 0 (Fun x []) P} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>(S' - {sub 0 (Fun x []) P}) \<union> {Exi P}\<close>

      assume \<open>S' \<subseteq> S \<union> {sub 0 (Fun x []) P}\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      moreover have \<open>\<forall>a \<in> ?S'. x \<notin> params a\<close>
        using \<open>\<forall>a \<in> S. x \<notin> params a\<close> \<open>?S' \<subseteq> S\<close> by blast
      ultimately have \<open>?S' \<union> {sub 0 (Fun x []) P} \<in> C\<close>
        using altconc \<open>\<forall>a \<in> S. x \<notin> params a\<close>
        unfolding alt_consistency_def by blast
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }

  { fix P x
    assume *: \<open>Neg (Uni P) \<in> S\<close> and \<open>\<forall>a \<in> S. x \<notin> params a\<close>
    show \<open>S \<union> {Neg (sub 0 (Fun x []) P)} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {Neg (sub 0 (Fun x []) P)} \<union> {Neg (Uni P)}\<close>

      assume \<open>S' \<subseteq> S \<union> {Neg (sub 0 (Fun x []) P)}\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      moreover have \<open>\<forall>a \<in> ?S'. x \<notin> params a\<close>
        using \<open>\<forall>a \<in> S. x \<notin> params a\<close> \<open>?S' \<subseteq> S\<close> by blast
      ultimately have \<open>?S' \<union> {Neg (sub 0 (Fun x []) P)} \<in> C\<close>
        using altconc \<open>\<forall>a \<in> S. x \<notin> params a\<close>
        unfolding alt_consistency_def by simp
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }
qed

theorem finite_char_closed: \<open>finite_char C \<Longrightarrow> subset_closed C\<close>
  unfolding finite_char_def subset_closed_def
proof (intro ballI allI impI)
  fix S S'
  assume *: \<open>\<forall>S. (S \<in> C) = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> C)\<close>
    and \<open>S' \<in> C\<close> and \<open>S \<subseteq> S'\<close>
  then have \<open>\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> C\<close> by blast
  then show \<open>S \<in> C\<close> using * by blast
qed

theorem finite_char_subset: \<open>subset_closed C \<Longrightarrow> C \<subseteq> mk_finite_char C\<close>
  unfolding mk_finite_char_def subset_closed_def by blast

subsection \<open>Enumerating datatypes\<close>

primrec diag :: \<open>nat \<Rightarrow> (nat \<times> nat)\<close> where
  \<open>diag 0 = (0, 0)\<close>
| \<open>diag (Suc n) =
     (let (x, y) = diag n
      in case y of
          0 \<Rightarrow> (0, Suc x)
        | Suc y \<Rightarrow> (Suc x, y))\<close>

theorem diag_le1: \<open>fst (diag (Suc n)) < Suc n\<close>
  by (induct n) (simp_all add: Let_def split_def split: nat.split)

theorem diag_le2: \<open>snd (diag (Suc (Suc n))) < Suc (Suc n)\<close>
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n')
  then show ?case proof (induct n')
    case 0
    then show ?case by simp
  next
    case (Suc _)
    then show ?case
      using diag_le1 by (simp add: Let_def split_def split: nat.split)
  qed
qed

theorem diag_le3: \<open>fst (diag n) = Suc x \<Longrightarrow> snd (diag n) < n\<close>
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n')
  then show ?case proof (induct n')
    case 0
    then show ?case by simp
  next
    case (Suc n'')
    then show ?case using diag_le2 by simp
  qed
qed

theorem diag_le4: \<open>fst (diag n) = Suc x \<Longrightarrow> x < n\<close>
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n')
  then have \<open>fst (diag (Suc n')) < Suc n'\<close>
    using diag_le1 by blast
  then show ?case using Suc by simp
qed

function undiag :: \<open>nat \<times> nat \<Rightarrow> nat\<close> where
  \<open>undiag (0, 0) = 0\<close>
| \<open>undiag (0, Suc y) = Suc (undiag (y, 0))\<close>
| \<open>undiag (Suc x, y) = Suc (undiag (x, Suc y))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(x, y). ((x + y) * (x + y + 1)) div 2 + x)\<close>) auto

theorem diag_undiag [simp]: \<open>diag (undiag (x, y)) = (x, y)\<close>
  by (induct rule: undiag.induct) simp_all

datatype btree = Leaf nat | Branch btree btree

function diag_btree :: \<open>nat \<Rightarrow> btree\<close> where
  \<open>diag_btree n = (case fst (diag n) of
       0 \<Rightarrow> Leaf (snd (diag n))
     | Suc x \<Rightarrow> Branch (diag_btree x) (diag_btree (snd (diag n))))\<close>
  by auto
termination
  by (relation \<open>measure id\<close>) (auto intro: diag_le3 diag_le4)

primrec undiag_btree :: \<open>btree \<Rightarrow> nat\<close> where
  \<open>undiag_btree (Leaf n) = undiag (0, n)\<close>
| \<open>undiag_btree (Branch t1 t2) =
     undiag (Suc (undiag_btree t1), undiag_btree t2)\<close>

theorem diag_undiag_btree [simp]: \<open>diag_btree (undiag_btree t) = t\<close>
  by (induct t) simp_all

declare diag_btree.simps [simp del] undiag_btree.simps [simp del]

fun list_of_btree :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> btree \<Rightarrow> 'a list\<close> where
  \<open>list_of_btree f (Leaf x) = []\<close>
| \<open>list_of_btree f (Branch (Leaf n) t) = f n # list_of_btree f t\<close>
| \<open>list_of_btree f _ = undefined\<close>

primrec btree_of_list :: \<open>('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> btree\<close> where
  \<open>btree_of_list f [] = Leaf 0\<close>
| \<open>btree_of_list f (x # xs) = Branch (Leaf (f x)) (btree_of_list f xs)\<close>

definition diag_list :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a list\<close> where
  \<open>diag_list f n = list_of_btree f (diag_btree n)\<close>

definition undiag_list :: \<open>('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat\<close> where
  \<open>undiag_list f xs = undiag_btree (btree_of_list f xs)\<close>

theorem diag_undiag_list [simp]: \<open>(\<And>x. d (u x) = x) \<Longrightarrow> diag_list d (undiag_list u xs) = xs\<close>
  by (induct xs) (simp_all add: diag_list_def undiag_list_def)

fun string_of_btree :: \<open>btree \<Rightarrow> string\<close> where
  \<open>string_of_btree (Leaf x) = []\<close>
| \<open>string_of_btree (Branch (Leaf n) t) = char_of n # string_of_btree t\<close>
| \<open>string_of_btree _ = undefined\<close>

primrec btree_of_string :: \<open>string \<Rightarrow> btree\<close> where
  \<open>btree_of_string [] = Leaf 0\<close>
| \<open>btree_of_string (x # xs) = Branch (Leaf (of_char x)) (btree_of_string xs)\<close>

definition diag_string :: \<open>nat \<Rightarrow> string\<close> where
  \<open>diag_string n = string_of_btree (diag_btree n)\<close>

definition undiag_string :: \<open>string \<Rightarrow> nat\<close> where
  \<open>undiag_string xs = undiag_btree (btree_of_string xs)\<close>

theorem diag_undiag_string [simp]: \<open>diag_string (undiag_string xs) = xs\<close>
  by (induct xs) (simp_all add: diag_string_def undiag_string_def)

lemma inj_undiag_string: \<open>inj undiag_string\<close>
  by (metis diag_undiag_string inj_onI)

fun
  term_of_btree :: \<open>btree \<Rightarrow> tm\<close> and
  term_list_of_btree :: \<open>btree \<Rightarrow> tm list\<close> where
  \<open>term_of_btree (Leaf m) = Var m\<close>
| \<open>term_of_btree (Branch (Leaf m) t) =
     Fun (diag_string m) (term_list_of_btree t)\<close>
| \<open>term_list_of_btree (Leaf m) = []\<close>
| \<open>term_list_of_btree (Branch t1 t2) =
     term_of_btree t1 # term_list_of_btree t2\<close>
| \<open>term_of_btree (Branch (Branch _ _) _) = undefined\<close>

primrec
  btree_of_term :: \<open>tm \<Rightarrow> btree\<close> and
  btree_of_term_list :: \<open>tm list \<Rightarrow> btree\<close> where
  \<open>btree_of_term (Var m) = Leaf m\<close>
| \<open>btree_of_term (Fun m ts) = Branch (Leaf (undiag_string m)) (btree_of_term_list ts)\<close>
| \<open>btree_of_term_list [] = Leaf 0\<close>
| \<open>btree_of_term_list (t # ts) = Branch (btree_of_term t) (btree_of_term_list ts)\<close>

theorem term_btree:
  shows \<open>term_of_btree (btree_of_term t) = t\<close>
    and \<open>term_list_of_btree (btree_of_term_list ts) = ts\<close>
  by (induct t and ts rule: btree_of_term.induct btree_of_term_list.induct) simp_all

definition diag_term :: \<open>nat \<Rightarrow> tm\<close> where
  \<open>diag_term n = term_of_btree (diag_btree n)\<close>

definition undiag_term :: \<open>tm \<Rightarrow> nat\<close> where
  \<open>undiag_term t = undiag_btree (btree_of_term t)\<close>

theorem diag_undiag_term [simp]: \<open>diag_term (undiag_term t) = t\<close>
  unfolding diag_term_def undiag_term_def using term_btree by simp

fun form_of_btree :: \<open>btree \<Rightarrow> fm\<close> where
  \<open>form_of_btree (Leaf 0) = Falsity\<close>
| \<open>form_of_btree (Branch (Leaf 0) (Branch (Leaf m) (Leaf n))) =
     Pre (diag_string m) (diag_list diag_term n)\<close>
| \<open>form_of_btree (Branch (Leaf (Suc 0)) (Branch t1 t2)) =
     Con (form_of_btree t1) (form_of_btree t2)\<close>
| \<open>form_of_btree (Branch (Leaf (Suc (Suc 0))) (Branch t1 t2)) =
     Dis (form_of_btree t1) (form_of_btree t2)\<close>
| \<open>form_of_btree (Branch (Leaf (Suc (Suc (Suc 0)))) (Branch t1 t2)) =
     Imp (form_of_btree t1) (form_of_btree t2)\<close>
| \<open>form_of_btree (Branch (Leaf (Suc (Suc (Suc (Suc 0))))) t) =
     Uni (form_of_btree t)\<close>
| \<open>form_of_btree (Branch (Leaf (Suc (Suc (Suc (Suc (Suc 0)))))) t) =
     Exi (form_of_btree t)\<close>
| \<open>form_of_btree (Leaf (Suc _)) = undefined\<close>
| \<open>form_of_btree (Branch (Leaf (Suc (Suc (Suc (Suc (Suc (Suc _))))))) _) = undefined\<close>
| \<open>form_of_btree (Branch (Leaf (Suc (Suc (Suc 0)))) (Leaf _)) = undefined\<close>
| \<open>form_of_btree (Branch (Leaf (Suc (Suc 0))) (Leaf _)) = undefined\<close>
| \<open>form_of_btree (Branch (Leaf (Suc 0)) (Leaf _)) = undefined\<close>
| \<open>form_of_btree (Branch (Branch _ _) _) = undefined\<close>
| \<open>form_of_btree (Branch (Leaf 0) (Leaf _)) = undefined\<close>
| \<open>form_of_btree (Branch (Leaf 0) (Branch (Branch _ _) _)) = undefined\<close>
| \<open>form_of_btree (Branch (Leaf 0) (Branch (Leaf _) (Branch _ _))) = undefined\<close>

primrec btree_of_form :: \<open>fm \<Rightarrow> btree\<close> where
  \<open>btree_of_form Falsity = Leaf 0\<close>
| \<open>btree_of_form (Pre b ts) = Branch (Leaf 0)
     (Branch (Leaf (undiag_string b)) (Leaf (undiag_list undiag_term ts)))\<close>
| \<open>btree_of_form (Con a b) = Branch (Leaf (Suc 0))
     (Branch (btree_of_form a) (btree_of_form b))\<close>
| \<open>btree_of_form (Dis a b) = Branch (Leaf (Suc (Suc 0)))
     (Branch (btree_of_form a) (btree_of_form b))\<close>
| \<open>btree_of_form (Imp a b) = Branch (Leaf (Suc (Suc (Suc 0))))
     (Branch (btree_of_form a) (btree_of_form b))\<close>
| \<open>btree_of_form (Uni a) = Branch (Leaf (Suc (Suc (Suc (Suc 0)))))
     (btree_of_form a)\<close>
| \<open>btree_of_form (Exi a) = Branch (Leaf (Suc (Suc (Suc (Suc (Suc 0))))))
     (btree_of_form a)\<close>

definition diag_form :: \<open>nat \<Rightarrow> fm\<close> where
  \<open>diag_form n = form_of_btree (diag_btree n)\<close>

definition undiag_form :: \<open>fm \<Rightarrow> nat\<close> where
  \<open>undiag_form x = undiag_btree (btree_of_form x)\<close>

theorem diag_undiag_form [simp]: \<open>diag_form (undiag_form f) = f\<close>
  unfolding diag_form_def undiag_form_def by (induct f) simp_all

definition diag_form' :: \<open>nat \<Rightarrow> fm\<close> where
  \<open>diag_form' = diag_form\<close>

definition undiag_form' :: \<open>fm \<Rightarrow> nat\<close> where
  \<open>undiag_form' = undiag_form\<close>

theorem diag_undiag_form' [simp]: \<open>diag_form' (undiag_form' f) = f\<close>
  by (simp add: diag_form'_def undiag_form'_def)

abbreviation \<open>from_nat \<equiv> diag_form'\<close>
abbreviation \<open>to_nat \<equiv> undiag_form'\<close>

subsection \<open>Extension to maximal consistent sets\<close>

definition is_chain :: \<open>(nat \<Rightarrow> 'a set) \<Rightarrow> bool\<close> where
  \<open>is_chain f = (\<forall>n. f n \<subseteq> f (Suc n))\<close>

lemma is_chainD: \<open>is_chain f \<Longrightarrow> x \<in> f m \<Longrightarrow> x \<in> f (m + n)\<close>
  unfolding is_chain_def by (induct n) auto

lemma is_chainD':
  assumes \<open>is_chain f\<close> and \<open>x \<in> f m\<close> and \<open>m \<le> k\<close>
  shows \<open>x \<in> f k\<close>
proof -
  have \<open>\<exists>n. k = m + n\<close>
    using \<open>m \<le> k\<close> by (simp add: le_iff_add)
  then obtain n where \<open>k = m + n\<close>
    by blast
  then show \<open>x \<in> f k\<close>
    using \<open>is_chain f\<close> \<open>x \<in> f m\<close>
    by (simp add: is_chainD)
qed

lemma chain_index:
  assumes ch: \<open>is_chain f\<close> and fin: \<open>finite F\<close>
  shows \<open>F \<subseteq> (\<Union>n. f n) \<Longrightarrow> \<exists>n. F \<subseteq> f n\<close>
  using fin
proof (induct rule: finite_induct)
  case empty
  then show ?case by blast
next
  case (insert x F)
  then have \<open>\<exists>n. F \<subseteq> f n\<close> and \<open>\<exists>m. x \<in> f m\<close> and \<open>F \<subseteq> (\<Union>x. f x)\<close>
    using ch by simp_all
  then obtain n and m where \<open>F \<subseteq> f n\<close> and \<open>x \<in> f m\<close>
    by blast
  have \<open>m \<le> max n m\<close> and \<open>n \<le> max n m\<close>
    by simp_all
  have \<open>x \<in> f (max n m)\<close>
    using is_chainD' ch \<open>x \<in> f m\<close> \<open>m \<le> max n m\<close> by fast
  moreover have \<open>F \<subseteq> f (max n m)\<close>
    using is_chainD' ch \<open>F \<subseteq> f n\<close> \<open>n \<le> max n m\<close> by fast
  ultimately show ?case by blast
qed

lemma chain_union_closed':
  assumes \<open>is_chain f\<close> and \<open>\<forall>n. f n \<in> C\<close> and \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
    and \<open>finite S'\<close> and \<open>S' \<subseteq> (\<Union>n. f n)\<close>
  shows \<open>S' \<in> C\<close>
proof -
  note \<open>finite S'\<close> and \<open>S' \<subseteq> (\<Union>n. f n)\<close>
  then obtain n where \<open>S' \<subseteq> f n\<close>
    using chain_index \<open>is_chain f\<close> by blast
  moreover have \<open>f n \<in> C\<close>
    using \<open>\<forall>n. f n \<in> C\<close> by blast
  ultimately show \<open>S' \<in> C\<close>
    using \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close> by blast
qed

theorem chain_union_closed:
  assumes \<open>finite_char C\<close> and \<open>is_chain f\<close> and \<open>\<forall>n. f n \<in> C\<close>
  shows \<open>(\<Union>n. f n) \<in> C\<close>
proof -
  have \<open>subset_closed C\<close>
    using finite_char_closed \<open>finite_char C\<close> by blast
  then have \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
    using subset_closed_def by blast
  then have \<open>\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> (\<Union>n. f n) \<longrightarrow> S' \<in> C\<close>
    using chain_union_closed' assms by blast
  moreover have \<open>((\<Union>n. f n) \<in> C) = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> (\<Union>n. f n) \<longrightarrow> S' \<in> C)\<close>
    using \<open>finite_char C\<close> unfolding finite_char_def by blast
  ultimately show ?thesis by blast
qed

abbreviation dest_Neg :: \<open>fm \<Rightarrow> fm\<close> where
  \<open>dest_Neg p \<equiv> (case p of (Imp p' Falsity) \<Rightarrow> p' | p' \<Rightarrow> p')\<close>

abbreviation dest_Uni :: \<open>fm \<Rightarrow> fm\<close> where
  \<open>dest_Uni p \<equiv> (case p of (Uni p') \<Rightarrow> p' | p' \<Rightarrow> p')\<close>

abbreviation dest_Exi :: \<open>fm \<Rightarrow> fm\<close> where
  \<open>dest_Exi p \<equiv> (case p of (Exi p') \<Rightarrow> p' | p' \<Rightarrow> p')\<close>

primrec extend :: \<open>fm set \<Rightarrow> fm set set \<Rightarrow> (nat \<Rightarrow> fm) \<Rightarrow> nat \<Rightarrow> fm set\<close> where
  \<open>extend S C f 0 = S\<close> |
  \<open>extend S C f (Suc n) = (if extend S C f n \<union> {f n} \<in> C
   then (if (\<exists>p. f n = Exi p)
      then extend S C f n \<union> {f n} \<union> {sub 0
        (Fun (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) [])
        (dest_Exi (f n))}
      else if (\<exists>p. f n = Neg (Uni p))
      then extend S C f n \<union> {f n} \<union> {Neg (sub 0
        (Fun (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) [])
        (dest_Uni (dest_Neg (f n))))}
      else extend S C f n \<union> {f n})
   else extend S C f n)\<close>

definition Extend :: \<open>fm set \<Rightarrow> fm set set \<Rightarrow> (nat \<Rightarrow> fm) \<Rightarrow> fm set\<close> where
  \<open>Extend S C f = (\<Union>n. extend S C f n)\<close>

theorem is_chain_extend: \<open>is_chain (extend S C f)\<close>
  by (simp add: is_chain_def) blast

lemma finite_params' [simp]: \<open>finite (params_term t)\<close> \<open>finite (params_list l)\<close>
  by (induct t and l rule: params_term.induct params_list.induct) simp_all

lemma finite_params [simp]: \<open>finite (params p)\<close>
  by (induct p) simp_all

lemma finite_params_extend [simp]:
  \<open>infinite (\<Inter>p \<in> S. - params p) \<Longrightarrow> infinite (\<Inter>p \<in> extend S C f n. - params p)\<close>
  by (induct n) (simp_all add: set_inter_compl_diff)

lemma infinite_params_available:
  assumes \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
  shows \<open>\<exists>x. x \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)\<close>
    (is \<open>_ (\<Union>_ \<in> ?S'. _)\<close>)
proof -
  have \<open>infinite (- (\<Union>p \<in> ?S'. params p))\<close>
    using assms by (simp add: set_inter_compl_diff)
  then obtain x where \<open>x \<in> - (\<Union>p \<in> ?S'. params p)\<close>
    using infinite_imp_nonempty by blast
  then show \<open>\<exists>x. x \<notin> (\<Union>p \<in> ?S'. params p)\<close>
    by blast
qed

lemma extend_in_C_Exi:
  assumes \<open>alt_consistency C\<close>
    and \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
    and \<open>extend S C f n \<union> {f n} \<in> C\<close> (is \<open>?S' \<in> C\<close>)
    and \<open>\<exists>p. f n = Exi p\<close>
  shows \<open>extend S C f (Suc n) \<in> C\<close>
proof -
  obtain p where *: \<open>f n = Exi p\<close>
    using \<open>\<exists>p. f n = Exi p\<close> by blast

  let ?x = \<open>(SOME k. k \<notin> (\<Union>p \<in> ?S'. params p))\<close>

  from \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
  have \<open>\<exists>x. x \<notin> (\<Union>p \<in> ?S'. params p)\<close>
    using infinite_params_available by blast
  then have \<open>?x \<notin> (\<Union>p \<in> ?S'. params p)\<close>
    using someI_ex by metis
  then have \<open>(?S' \<union> {sub 0 (Fun ?x []) p}) \<in> C\<close>
    using * \<open>?S' \<in> C\<close> \<open>alt_consistency C\<close>
    unfolding alt_consistency_def by simp
  then show ?thesis
    using assms * by simp
qed

lemma extend_in_C_Neg_Uni:
  assumes \<open>alt_consistency C\<close>
    and \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
    and \<open>extend S C f n \<union> {f n} \<in> C\<close> (is \<open>?S' \<in> C\<close>)
    and \<open>\<forall>p. f n \<noteq> Exi p\<close>
    and \<open>\<exists>p. f n = Neg (Uni p)\<close>
  shows \<open>extend S C f (Suc n) \<in> C\<close>
proof -
  obtain p where *: \<open>f n = Neg (Uni p)\<close>
    using \<open>\<exists>p. f n = Neg (Uni p)\<close> by blast

  let ?x = \<open>(SOME k. k \<notin> (\<Union>p \<in> ?S'. params p))\<close>

  have \<open>\<exists>x. x \<notin> (\<Union>p \<in> ?S'. params p)\<close>
    using \<open>infinite (- (\<Union>p \<in> S. params p))\<close> infinite_params_available by blast
  then have \<open>?x \<notin> (\<Union>p \<in> ?S'. params p)\<close>
    using someI_ex by metis
  moreover have \<open>Neg (Uni p) \<in> ?S'\<close>
    using * by simp
  ultimately have \<open>?S' \<union> {Neg (sub 0 (Fun ?x []) p)} \<in> C\<close>
    using \<open>?S' \<in> C\<close> \<open>alt_consistency C\<close> unfolding alt_consistency_def by simp
  then show ?thesis
    using assms * by simp
qed

lemma extend_in_C_no_delta:
  assumes \<open>extend S C f n \<union> {f n} \<in> C\<close>
    and \<open>\<forall>p. f n \<noteq> Exi p\<close>
    and \<open>\<forall>p. f n \<noteq> Neg (Uni p)\<close>
  shows \<open>extend S C f (Suc n) \<in> C\<close>
  using assms by simp

lemma extend_in_C_stop:
  assumes \<open>extend S C f n \<in> C\<close>
    and \<open>extend S C f n \<union> {f n} \<notin> C\<close>
  shows \<open>extend S C f (Suc n) \<in> C\<close>
  using assms by simp

theorem extend_in_C:
  \<open>alt_consistency C \<Longrightarrow> S \<in> C \<Longrightarrow> infinite (- (\<Union>p \<in> S. params p)) \<Longrightarrow> extend S C f n \<in> C\<close>
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    using extend_in_C_Exi extend_in_C_Neg_Uni
      extend_in_C_no_delta extend_in_C_stop by metis
qed

theorem Extend_in_C: \<open>alt_consistency C \<Longrightarrow> finite_char C \<Longrightarrow>
    S \<in> C \<Longrightarrow> infinite (- (\<Union>p \<in> S. params p)) \<Longrightarrow> Extend S C f \<in> C\<close>
  using chain_union_closed is_chain_extend extend_in_C
  unfolding Extend_def by blast

theorem Extend_subset: \<open>S \<subseteq> Extend S C f\<close>
  unfolding Extend_def using Union_upper extend.simps(1) range_eqI by metis

definition maximal :: \<open>'a set \<Rightarrow> 'a set set \<Rightarrow> bool\<close> where
  \<open>maximal S C = (\<forall>S' \<in> C. S \<subseteq> S' \<longrightarrow> S = S')\<close>

theorem Extend_maximal:
  assumes \<open>\<forall>y :: fm. \<exists>n. y = f n\<close> and \<open>finite_char C\<close>
  shows \<open>maximal (Extend S C f) C\<close>
  unfolding maximal_def Extend_def
proof (intro ballI impI)
  fix S'
  assume \<open>S' \<in> C\<close> and \<open>(\<Union>x. extend S C f x) \<subseteq> S'\<close>
  moreover have \<open>S' \<subseteq> (\<Union>x. extend S C f x)\<close>
  proof (rule ccontr)
    assume \<open>\<not> S' \<subseteq> (\<Union>x. extend S C f x)\<close>
    then obtain z where \<open>z \<in> S'\<close> and *: \<open>z \<notin> (\<Union>x. extend S C f x)\<close>
      by blast
    then obtain n where \<open>z = f n\<close>
      using \<open>\<forall>y. \<exists>n. y = f n\<close> by blast

    from \<open>(\<Union>x. extend S C f x) \<subseteq> S'\<close> \<open>z = f n\<close> \<open>z \<in> S'\<close>
    have \<open>extend S C f n \<union> {f n} \<subseteq> S'\<close> by blast

    from \<open>finite_char C\<close>
    have \<open>subset_closed C\<close> using finite_char_closed by blast
    then have \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
      unfolding subset_closed_def by simp
    then have \<open>\<forall>S \<subseteq> S'. S \<in> C\<close>
      using \<open>S' \<in> C\<close> by blast
    then have \<open>extend S C f n \<union> {f n} \<in> C\<close>
      using \<open>extend S C f n \<union> {f n} \<subseteq> S'\<close> by blast
    then have \<open>z \<in> extend S C f (Suc n)\<close>
      using \<open>z \<notin> (\<Union>x. extend S C f x)\<close> \<open>z = f n\<close> by simp
    then show False using * by blast
  qed
  ultimately show \<open>(\<Union>x. extend S C f x) = S'\<close>
    by simp
qed

subsection \<open>Hintikka sets and Herbrand models\<close>

definition hintikka :: \<open>fm set \<Rightarrow> bool\<close> where
  \<open>hintikka H =
    ((\<forall>p ts. \<not> (Pre p ts \<in> H \<and> Neg (Pre p ts) \<in> H)) \<and>
    Falsity \<notin> H \<and>
    (\<forall>Z. Neg (Neg Z) \<in> H \<longrightarrow> Z \<in> H) \<and>
    (\<forall>A B. Con A B \<in> H \<longrightarrow> A \<in> H \<and> B \<in> H) \<and>
    (\<forall>A B. Neg (Dis A B) \<in> H \<longrightarrow> Neg A \<in> H \<and> Neg B \<in> H) \<and>
    (\<forall>A B. Dis A B \<in> H \<longrightarrow> A \<in> H \<or> B \<in> H) \<and>
    (\<forall>A B. Neg (Con A B) \<in> H \<longrightarrow> Neg A \<in> H \<or> Neg B \<in> H) \<and>
    (\<forall>A B. Imp A B \<in> H \<longrightarrow> Neg A \<in> H \<or> B \<in> H) \<and>
    (\<forall>A B. Neg (Imp A B) \<in> H \<longrightarrow> A \<in> H \<and> Neg B \<in> H) \<and>
    (\<forall>P t. closed_term 0 t \<longrightarrow> Uni P \<in> H \<longrightarrow> sub 0 t P \<in> H) \<and>
    (\<forall>P t. closed_term 0 t \<longrightarrow> Neg (Exi P) \<in> H \<longrightarrow> Neg (sub 0 t P) \<in> H) \<and>
    (\<forall>P. Exi P \<in> H \<longrightarrow> (\<exists>t. closed_term 0 t \<and> sub 0 t P \<in> H)) \<and>
    (\<forall>P. Neg (Uni P) \<in> H \<longrightarrow> (\<exists>t. closed_term 0 t \<and> Neg (sub 0 t P) \<in> H)))\<close>

datatype htm = HFun id \<open>htm list\<close>

primrec
  tm_of_htm :: \<open>htm \<Rightarrow> tm\<close> and
  tms_of_htms :: \<open>htm list \<Rightarrow> tm list\<close> where
  \<open>tm_of_htm (HFun a hts) = Fun a (tms_of_htms hts)\<close> |
  \<open>tms_of_htms [] = []\<close> |
  \<open>tms_of_htms (ht # hts) = tm_of_htm ht # tms_of_htms hts\<close>

lemma herbrand_semantics [simp]:
  \<open>closed_term 0 t \<Longrightarrow> tm_of_htm (semantics_term e HFun t) = t\<close>
  \<open>closed_list 0 l \<Longrightarrow> tms_of_htms (semantics_list e HFun l) = l\<close>
  by (induct t and l rule: closed_term.induct closed_list.induct) simp_all

lemma herbrand_semantics' [simp]:
  \<open>semantics_term e HFun (tm_of_htm ht) = ht\<close>
  \<open>semantics_list e HFun (tms_of_htms hts) = hts\<close>
  by (induct ht and hts rule: tm_of_htm.induct tms_of_htms.induct) simp_all

theorem closed_htm [simp]:
  \<open>closed_term 0 (tm_of_htm ht)\<close>
  \<open>closed_list 0 (tms_of_htms hts)\<close>
  by (induct ht and hts rule: tm_of_htm.induct tms_of_htms.induct) simp_all

theorem hintikka_model:
  assumes hin: \<open>hintikka H\<close>
  shows \<open>(p \<in> H \<longrightarrow> closed 0 p \<longrightarrow> semantics e HFun (\<lambda>i l. Pre i (tms_of_htms l) \<in> H) p) \<and>
     (Neg p \<in> H \<longrightarrow> closed 0 p \<longrightarrow> semantics e HFun (\<lambda>i l. Pre i (tms_of_htms l) \<in> H) (Neg p))\<close>
proof (induct p rule: wf_induct)
  show \<open>wf (measure size_formulas)\<close>
    by blast
next
  let ?semantics = \<open>semantics e HFun (\<lambda>i l. Pre i (tms_of_htms l) \<in> H)\<close>

  fix x
  assume wf: \<open>\<forall>y. (y, x) \<in> measure size_formulas \<longrightarrow>
      (y \<in> H \<longrightarrow> closed 0 y \<longrightarrow> ?semantics y) \<and>
  (Neg y \<in> H \<longrightarrow> closed 0 y \<longrightarrow> ?semantics (Neg y))\<close>

  show \<open>(x \<in> H \<longrightarrow> closed 0 x \<longrightarrow> ?semantics x) \<and>
    (Neg x \<in> H \<longrightarrow> closed 0 x \<longrightarrow> ?semantics (Neg x))\<close>
  proof (cases x)
    case Falsity
    show ?thesis proof (intro conjI impI)
      assume \<open>x \<in> H\<close>
      then show \<open>?semantics x\<close>
        using Falsity hin by (simp add: hintikka_def)
    next
      assume \<open>Neg x \<in> H\<close>
      then show \<open>?semantics (Neg x)\<close>
        using Falsity by simp
    qed
  next
    case (Pre p ts)
    show ?thesis proof (intro conjI impI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      then show \<open>?semantics x\<close> using Pre by simp
    next
      assume \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Neg (Pre p ts) \<in> H\<close>
        using Pre by simp
      then have \<open>Pre p ts \<notin> H\<close>
        using hin unfolding hintikka_def by fast
      then show \<open>?semantics (Neg x)\<close>
        using Pre \<open>closed 0 x\<close> by simp
    qed
  next
    case (Con A B)
    then show ?thesis proof (intro conjI impI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Con A B \<in> H\<close> and \<open>closed 0 (Con A B)\<close>
        using Con by simp_all
      then have \<open>A \<in> H \<and> B \<in> H\<close>
        using Con hin unfolding hintikka_def by blast
      then show \<open>?semantics x\<close>
        using Con wf \<open>closed 0 (Con A B)\<close> by simp
    next
      assume \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Neg (Con A B) \<in> H\<close> and \<open>closed 0 (Con A B)\<close>
        using Con by simp_all
      then have \<open>Neg A \<in> H \<or> Neg B \<in> H\<close>
        using hin unfolding hintikka_def by blast
      then show \<open>?semantics (Neg x)\<close>
        using Con wf \<open>closed 0 (Con A B)\<close> by force
    qed
  next
    case (Dis A B)
    then show ?thesis proof (intro conjI impI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Dis A B \<in> H\<close> and \<open>closed 0 (Dis A B)\<close>
        using Dis by simp_all
      then have \<open>A \<in> H \<or> B \<in> H\<close>
        using hin unfolding hintikka_def by blast
      then show \<open>?semantics x\<close>
        using Dis wf \<open>closed 0 (Dis A B)\<close> by fastforce
    next
      assume \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Neg (Dis A B) \<in> H\<close> and \<open>closed 0 (Dis A B)\<close>
        using Dis by simp_all
      then have \<open>Neg A \<in> H \<and> Neg B \<in> H\<close>
        using hin unfolding hintikka_def by blast
      then show \<open>?semantics (Neg x)\<close>
        using Dis wf \<open>closed 0 (Dis A B)\<close> by force
    qed
  next
    case (Imp A B)
    then show ?thesis proof (intro conjI impI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Imp A B \<in> H\<close> and \<open>closed 0 (Imp A B)\<close>
        using Imp by simp_all
      then have \<open>Neg A \<in> H \<or> B \<in> H\<close>
        using hin unfolding hintikka_def by blast
      then show \<open>?semantics x\<close>
        using Imp wf \<open>closed 0 (Imp A B)\<close> by force
    next
      assume \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Neg (Imp A B) \<in> H\<close> and \<open>closed 0 (Imp A B)\<close>
        using Imp by simp_all
      then have \<open>A \<in> H \<and> Neg B \<in> H\<close>
        using hin unfolding hintikka_def by blast
      then show \<open>?semantics (Neg x)\<close>
        using Imp wf \<open>closed 0 (Imp A B)\<close> by force
    qed
  next
    case (Uni P)
    then show ?thesis proof (intro conjI impI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      have \<open>\<forall>z. semantics (put e 0 z) HFun (\<lambda>a ts. Pre a (tms_of_htms ts) \<in> H) P\<close>
      proof (rule allI)
        fix z
        from \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
        have \<open>Uni P \<in> H\<close> and \<open>closed 0 (Uni P)\<close>
          using Uni by simp_all
        then have *: \<open>\<forall>P t. closed_term 0 t \<longrightarrow> Uni P \<in> H \<longrightarrow> sub 0 t P \<in> H\<close>
          using hin unfolding hintikka_def by blast
        from \<open>closed 0 (Uni P)\<close>
        have \<open>closed (Suc 0) P\<close> by simp

        have \<open>(sub 0 (tm_of_htm z) P, Uni P) \<in> measure size_formulas \<longrightarrow>
              (sub 0 (tm_of_htm z) P \<in> H \<longrightarrow> closed 0 (sub 0 (tm_of_htm z) P) \<longrightarrow>
              ?semantics (sub 0 (tm_of_htm z) P))\<close>
          using Uni wf by blast
        then show \<open>semantics (put e 0 z) HFun (\<lambda>a ts. Pre a (tms_of_htms ts) \<in> H) P\<close>
          using * \<open>Uni P \<in> H\<close> \<open>closed (Suc 0) P\<close> by simp
      qed
      then show \<open>?semantics x\<close>
        using Uni by simp
    next
      assume \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Neg (Uni P) \<in> H\<close>
        using Uni by simp
      then have \<open>\<exists>t. closed_term 0 t \<and> Neg (sub 0 t P) \<in> H\<close>
        using Uni hin unfolding hintikka_def by blast
      then obtain t where *: \<open>closed_term 0 t \<and> Neg (sub 0 t P) \<in> H\<close>
        by blast
      then have \<open>closed 0 (sub 0 t P)\<close>
        using Uni \<open>closed 0 x\<close> by simp

      have \<open>(sub 0 t P, Uni P) \<in> measure size_formulas \<longrightarrow>
              (Neg (sub 0 t P) \<in> H \<longrightarrow> closed 0 (sub 0 t P) \<longrightarrow>
              ?semantics (Neg (sub 0 t P)))\<close>
        using Uni wf by blast
      then have \<open>?semantics (Neg (sub 0 t P))\<close>
        using Uni * \<open>closed 0 (sub 0 t P)\<close> by simp
      then have \<open>\<exists>z. \<not> semantics (put e 0 z) HFun (\<lambda>a ts. Pre a (tms_of_htms ts) \<in> H) P\<close>
        by (meson semantics.simps(1,3) substitute)
      then show \<open>?semantics (Neg x)\<close>
        using Uni by simp
    qed
  next
    case (Exi P)
    then show ?thesis proof (intro conjI impI allI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>\<exists>t. closed_term 0 t \<and> (sub 0 t P) \<in> H\<close>
        using Exi hin unfolding hintikka_def by blast
      then obtain t where *: \<open>closed_term 0 t \<and> (sub 0 t P) \<in> H\<close>
        by blast
      then have \<open>closed 0 (sub 0 t P)\<close>
        using Exi \<open>closed 0 x\<close> by simp

      have \<open>(sub 0 t P, Exi P) \<in> measure size_formulas \<longrightarrow>
              (sub 0 t P \<in> H \<longrightarrow> closed 0 (sub 0 t P) \<longrightarrow>
              ?semantics (sub 0 t P))\<close>
        using Exi wf by blast
      then have \<open>?semantics (sub 0 t P)\<close>
        using Exi * \<open>closed 0 (sub 0 t P)\<close> by simp
      then have \<open>\<exists>z. semantics (put e 0 z) HFun (\<lambda>a ts. Pre a (tms_of_htms ts) \<in> H) P\<close>
        by auto
      then show \<open>?semantics x\<close>
        using Exi by simp
    next
      assume \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
      have \<open>\<forall>z. \<not> semantics (put e 0 z) HFun (\<lambda>a ts. Pre a (tms_of_htms ts) \<in> H) P\<close>
      proof (rule allI)
        fix z
        from \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
        have \<open>Neg (Exi P) \<in> H\<close> and \<open>closed 0 (Neg (Exi P))\<close>
          using Exi by simp_all
        then have *: \<open>\<forall>P t. closed_term 0 t \<longrightarrow> Neg (Exi P) \<in> H \<longrightarrow> Neg (sub 0 t P) \<in> H\<close>
          using hin unfolding hintikka_def by blast
        from \<open>closed 0 (Neg (Exi P))\<close>
        have \<open>closed (Suc 0) P\<close> by simp

        have \<open>(sub 0 (tm_of_htm z) P, Exi P) \<in> measure size_formulas \<longrightarrow>
              (Neg (sub 0 (tm_of_htm z) P) \<in> H \<longrightarrow> closed 0 (sub 0 (tm_of_htm z) P) \<longrightarrow>
              ?semantics (Neg (sub 0 (tm_of_htm z) P)))\<close>
          using Exi wf by blast
        then show \<open>\<not> semantics (put e 0 z) HFun (\<lambda>a ts. Pre a (tms_of_htms ts) \<in> H) P\<close>
          using * \<open>Neg (Exi P) \<in> H\<close> \<open>closed (Suc 0) P\<close> by auto
      qed
      then show \<open>?semantics (Neg x)\<close>
        using Exi by simp
    qed
  qed
qed

lemma Exi_in_extend:
  assumes \<open>extend S C f n \<union> {f n} \<in> C\<close> (is \<open>?S' \<in> C\<close>)
    and \<open>Exi P = f n\<close>
  shows \<open>sub 0 (Fun (SOME k. k \<notin> (\<Union>p \<in> ?S'. params p)) []) P \<in> extend S C f (Suc n)\<close>
    (is \<open>sub 0 ?t P \<in> _\<close>)
proof -
  have \<open>\<exists>p. f n = Exi p\<close>
    using \<open>Exi P = f n\<close> by metis
  then have \<open>extend S C f (Suc n) = (?S' \<union> {sub 0 ?t (dest_Exi (f n))})\<close>
    using \<open>?S' \<in> C\<close> by simp
  also have \<open>\<dots> = (?S' \<union> {sub 0 ?t (dest_Exi (Exi P))})\<close>
    using \<open>Exi P = f n\<close> by simp
  also have \<open>\<dots> = (?S' \<union> {sub 0 ?t P})\<close>
    by simp
  finally show ?thesis
    by blast
qed

lemma Neg_Uni_in_extend:
  assumes \<open>extend S C f n \<union> {f n} \<in> C\<close> (is \<open>?S' \<in> C\<close>)
    and \<open>Neg (Uni P) = f n\<close>
  shows \<open>Neg (sub 0 (Fun (SOME k. k \<notin> (\<Union>p \<in> ?S'. params p)) []) P) \<in> extend S C f (Suc n)\<close>
    (is \<open>Neg (sub 0 ?t P) \<in> _\<close>)
proof -
  have \<open>f n \<noteq> Exi P\<close>
    using \<open>Neg (Uni P) = f n\<close> by auto

  have \<open>\<exists>p. f n = Neg (Uni p)\<close>
    using \<open>Neg (Uni P) = f n\<close> by metis
  then have \<open>extend S C f (Suc n) = (?S' \<union> {Neg (sub 0 ?t (dest_Uni (dest_Neg (f n))))})\<close>
    using \<open>?S' \<in> C\<close> \<open>f n \<noteq> Exi P\<close> by auto
  also have \<open>\<dots> = (?S' \<union> {Neg (sub 0 ?t (dest_Uni (dest_Neg (Neg (Uni P)))))})\<close>
    using \<open>Neg (Uni P) = f n\<close> by simp
  also have \<open>\<dots> = (?S' \<union> {Neg (sub 0 ?t P)})\<close>
    by simp
  finally show ?thesis
    by blast
qed

theorem extend_hintikka:
  assumes \<open>S \<in> C\<close>
    and fin_ch: \<open>finite_char C\<close>
    and infin_p: \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
    and surj: \<open>\<forall>y. \<exists>n. y = f n\<close>
    and altc: \<open>alt_consistency C\<close>
  shows \<open>hintikka (Extend S C f)\<close> (is \<open>hintikka ?H\<close>)
  unfolding hintikka_def
proof (intro allI impI conjI)
  have \<open>maximal ?H C\<close> and \<open>?H \<in> C\<close>
    using Extend_maximal Extend_in_C assms by blast+

  { fix p ts
    show \<open>\<not> (Pre p ts \<in> ?H \<and> Neg (Pre p ts) \<in> ?H)\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast }

  show \<open>Falsity \<notin> ?H\<close>
    using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by blast

  { fix Z
    assume \<open>Neg (Neg Z) \<in> ?H\<close>
    then have \<open>?H \<union> {Z} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast
    then show \<open>Z \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }

  { fix A B
    assume \<open>Con A B \<in> ?H\<close>
    then have \<open>?H \<union> {A, B} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast
    then show \<open>A \<in> ?H\<close> and \<open>B \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast+ }

  { fix A B
    assume \<open>Neg (Dis A B) \<in> ?H\<close>
    then have \<open>?H \<union> {Neg A, Neg B} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast
    then show \<open>Neg A \<in> ?H\<close> and \<open>Neg B \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast+ }

  { fix A B
    assume \<open>Neg (Imp A B) \<in> ?H\<close>
    then have \<open>?H \<union> {A, Neg B} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by blast
    then show \<open>A \<in> ?H\<close> and \<open>Neg B \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast+ }

  { fix A B
    assume \<open>Dis A B \<in> ?H\<close>
    then have \<open>?H \<union> {A} \<in> C \<or> ?H \<union> {B} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast
    then show \<open>A \<in> ?H \<or> B \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }

  { fix A B
    assume \<open>Neg (Con A B) \<in> ?H\<close>
    then have \<open>?H \<union> {Neg A} \<in> C \<or> ?H \<union> {Neg B} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by simp
    then show \<open>Neg A \<in> ?H \<or> Neg B \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }

  { fix A B
    assume \<open>Imp A B \<in> ?H\<close>
    then have \<open>?H \<union> {Neg A} \<in> C \<or> ?H \<union> {B} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by simp
    then show \<open>Neg A \<in> ?H \<or> B \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }

  { fix P t
    assume \<open>Uni P \<in> ?H\<close> and \<open>closed_term 0 t\<close>
    then have \<open>?H \<union> {sub 0 t P} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by blast
    then show \<open>sub 0 t P \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }

  { fix P t
    assume \<open>Neg (Exi P) \<in> ?H\<close> and \<open>closed_term 0 t\<close>
    then have \<open>?H \<union> {Neg (sub 0 t P)} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by blast
    then show \<open>Neg (sub 0 t P) \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }

  { fix P
    assume \<open>Exi P \<in> ?H\<close>
    obtain n where *: \<open>Exi P = f n\<close>
      using surj by blast

    let ?t = \<open>Fun (SOME k.
      k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) []\<close>

    have \<open>closed_term 0 ?t\<close>
      by simp

    moreover have \<open>extend S C f n \<union> {f n} \<subseteq> ?H\<close>
      using \<open>Exi P \<in> ?H\<close> * Extend_def by (simp add: UN_upper)
    then have \<open>extend S C f n \<union> {f n} \<in> C\<close>
      using \<open>?H \<in> C\<close> fin_ch finite_char_closed subset_closed_def by metis
    then have \<open>sub 0 ?t P \<in> ?H\<close>
      using * Exi_in_extend Extend_def by fast
    ultimately show \<open>\<exists>t. closed_term 0 t \<and> sub 0 t P \<in> ?H\<close>
      by blast }

  { fix P
    assume \<open>Neg (Uni P) \<in> ?H\<close>
    obtain n where *: \<open>Neg (Uni P) = f n\<close>
      using surj by blast

    let ?t = \<open>Fun (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) []\<close>

    have \<open>closed_term 0 ?t\<close>
      by simp

    moreover have \<open>extend S C f n \<union> {f n} \<subseteq> ?H\<close>
      using \<open>Neg (Uni P) \<in> ?H\<close> * Extend_def by (simp add: UN_upper)
    then have \<open>extend S C f n \<union> {f n} \<in> C\<close>
      using \<open>?H \<in> C\<close> fin_ch finite_char_closed subset_closed_def by metis
    then have \<open>Neg (sub 0 ?t P) \<in> ?H\<close>
      using * Neg_Uni_in_extend Extend_def by fast
    ultimately show \<open>\<exists>t. closed_term 0 t \<and> Neg (sub 0 t P) \<in> ?H\<close>
      by blast }
qed

subsection \<open>Model existence\<close>

lemma hintikka_Extend_S:
  assumes \<open>consistency C\<close> and \<open>S \<in> C\<close>
    and \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
  defines \<open>C' \<equiv> mk_finite_char (mk_alt_consistency (close C))\<close>
  shows \<open>hintikka (Extend S C' from_nat)\<close>
proof -
  have \<open>finite_char C'\<close>
    using C'_def finite_char by blast
  moreover have \<open>\<forall>y. y = from_nat (to_nat y)\<close>
    by simp
  then have \<open>\<forall>y. \<exists>n. y = from_nat n\<close>
    by blast
  moreover have \<open>alt_consistency C'\<close>
    using C'_def \<open>consistency C\<close> finite_alt_consistency alt_consistency
      close_closed close_consistency mk_alt_consistency_closed
    by blast
  moreover have \<open>S \<in> close C\<close>
    using close_subset \<open>S \<in> C\<close> by blast
  then have \<open>S \<in> mk_alt_consistency (close C)\<close>
    using mk_alt_consistency_subset by blast
  then have \<open>S \<in> C'\<close>
    using C'_def close_closed finite_char_subset mk_alt_consistency_closed by blast
  ultimately show ?thesis
    using extend_hintikka \<open>infinite (- (\<Union>p \<in> S. params p))\<close> by metis
qed

theorem model_existence:
  assumes \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
    and \<open>p \<in> S\<close> \<open>closed 0 p\<close>
    and \<open>S \<in> C\<close> \<open>consistency C\<close>
  defines \<open>C' \<equiv> mk_finite_char (mk_alt_consistency (close C))\<close>
  defines \<open>H \<equiv> Extend S C' from_nat\<close>
  shows \<open>semantics e HFun (\<lambda>a ts. Pre a (tms_of_htms ts) \<in> H) p\<close>
  using assms hintikka_model hintikka_Extend_S Extend_subset by blast

subsection \<open>Completeness using Herbrand terms\<close>

theorem OK_consistency: \<open>consistency {set G |G. \<not> (OK Falsity G)}\<close>
  unfolding consistency_def
proof (intro conjI allI impI notI)
  fix S
  assume \<open>S \<in> {set G |G. \<not> (OK Falsity G)}\<close> (is \<open>S \<in> ?C\<close>)
  then obtain G where *: \<open>S = set G\<close> and \<open>\<not> (OK Falsity G)\<close>
    by blast

  { fix i l
    assume \<open>Pre i l \<in> S \<and> Neg (Pre i l) \<in> S\<close>
    then have \<open>OK (Pre i l) G\<close> and \<open>OK (Neg (Pre i l)) G\<close>
      using Assume * by auto
    then have \<open>OK Falsity G\<close>
      using Imp_E by blast
    then show False
      using \<open>\<not> (OK Falsity G)\<close> by blast }

  { assume \<open>Falsity \<in> S\<close>
    then have \<open>OK Falsity G\<close>
      using Assume * by simp
    then show False
      using \<open>\<not> (OK Falsity G)\<close> by blast }

  { fix Z
    assume \<open>Neg (Neg Z) \<in> S\<close>
    then have \<open>OK (Neg (Neg Z)) G\<close>
      using Assume * by simp

    { assume \<open>OK Falsity (Z # G)\<close>
      then have \<open>OK (Neg Z) G\<close>
        using Imp_I by blast
      then have \<open>OK Falsity G\<close>
        using Imp_E \<open>OK (Neg (Neg Z)) G\<close> by blast
      then have False
        using \<open>\<not> (OK Falsity G)\<close> by blast }
    then have \<open>\<not> (OK Falsity (Z # G))\<close>
      by blast
    moreover have \<open>S \<union> {Z} = set (Z # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {Z} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Con A B \<in> S\<close>
    then have \<open>OK (Con A B) G\<close>
      using Assume * by simp
    then have \<open>OK A G\<close> and \<open>OK B G\<close>
      using Con_E1 Con_E2 by blast+

    { assume \<open>OK Falsity (A # B # G)\<close>
      then have \<open>OK (Neg A) (B # G)\<close>
        using Imp_I by blast
      then have \<open>OK (Neg A) G\<close>
        using cut \<open>OK B G\<close> by blast
      then have \<open>OK Falsity G\<close>
        using Imp_E \<open>OK A G\<close> by blast
      then have False
        using \<open>\<not> (OK Falsity G)\<close> by blast }
    then have \<open>\<not> (OK Falsity (A # B # G))\<close>
      by blast
    moreover have \<open>S \<union> {A, B} = set (A # B # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {A, B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Neg (Dis A B) \<in> S\<close>
    then have \<open>OK (Neg (Dis A B)) G\<close>
      using Assume * by simp

    have \<open>OK A (A # Neg B # G)\<close>
      using Assume by simp
    then have \<open>OK (Dis A B) (A # Neg B # G)\<close>
      using Dis_I1 by blast
    moreover have \<open>OK (Neg (Dis A B)) (A # Neg B # G)\<close>
      using * \<open>Neg (Dis A B) \<in> S\<close> Assume by simp
    ultimately have \<open>OK Falsity (A # Neg B # G)\<close>
      using Imp_E \<open>OK (Neg (Dis A B)) (A # Neg B # G)\<close> by blast
    then have \<open>OK (Neg A) (Neg B # G)\<close>
      using Imp_I by blast

    have \<open>OK B (B # G)\<close>
      using Assume by simp
    then have \<open>OK (Dis A B) (B # G)\<close>
      using Dis_I2 by blast
    moreover have \<open>OK (Neg (Dis A B)) (B # G)\<close>
      using * \<open>Neg (Dis A B) \<in> S\<close> Assume by simp
    ultimately have \<open>OK Falsity (B # G)\<close>
      using Imp_E \<open>OK (Neg (Dis A B)) (B # G)\<close> by blast
    then have \<open>OK (Neg B) G\<close>
      using Imp_I by blast

    { assume \<open>OK Falsity (Neg A # Neg B # G)\<close>
      then have \<open>OK (Neg (Neg A)) (Neg B # G)\<close>
        using Imp_I by blast
      then have \<open>OK Falsity (Neg B # G)\<close>
        using Imp_E \<open>OK (Neg A) (Neg B # G)\<close> by blast
      then have \<open>OK Falsity G\<close>
        using cut \<open>OK (Neg B) G\<close> by blast
      then have False
        using \<open>\<not> (OK Falsity G)\<close> by blast }
    then have \<open>\<not> (OK Falsity (Neg A # Neg B # G))\<close>
      by blast
    moreover have \<open>S \<union> {Neg A, Neg B} = set (Neg A # Neg B # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {Neg A, Neg B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Neg (Imp A B) \<in> S\<close>

    have \<open>OK A (A # Neg A # Neg B # G)\<close>
      using Assume by simp
    moreover have \<open>OK (Neg A) (A # Neg A # Neg B # G)\<close>
      using Assume by simp
    ultimately have \<open>OK Falsity (A # Neg A # Neg B # G)\<close>
      using Imp_E by blast
    then have \<open>OK B (A # Neg A # Neg B # G)\<close>
      using Falsity_E by blast
    then have \<open>OK (Imp A B) (Neg A # Neg B # G)\<close>
      using Imp_I by blast
    moreover have \<open>OK (Neg (Imp A B)) (Neg A # Neg B # G)\<close>
      using * \<open>Neg (Imp A B) \<in> S\<close> Assume by simp
    ultimately have \<open>OK Falsity (Neg A # Neg B # G)\<close>
      using Imp_E by blast
    then have \<open>OK A (Neg B # G)\<close>
      using Boole by blast

    have \<open>OK B (A # B # G)\<close>
      using Assume by simp
    then have \<open>OK (Imp A B) (B # G)\<close>
      using Imp_I by blast
    moreover have \<open>OK (Neg (Imp A B)) (B # G)\<close>
      using * \<open>Neg (Imp A B) \<in> S\<close> Assume by simp
    ultimately have \<open>OK Falsity (B # G)\<close>
      using Imp_E by blast
    then have \<open>OK (Neg B) G\<close>
      using Imp_I by blast

    { assume \<open>OK Falsity (A # Neg B # G)\<close>
      then have \<open>OK (Neg A) (Neg B # G)\<close>
        using Imp_I by blast
      then have \<open>OK Falsity (Neg B # G)\<close>
        using Imp_E \<open>OK A (Neg B # G)\<close> by blast
      then have \<open>OK Falsity G\<close>
        using cut \<open>OK (Neg B) G\<close> by blast
      then have False
        using \<open>\<not> (OK Falsity G)\<close> by blast }
    then have \<open>\<not> (OK Falsity (A # Neg B # G))\<close>
      by blast
    moreover have \<open>{A, Neg B} \<union> S = set (A # Neg B # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {A, Neg B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Dis A B \<in> S\<close>
    then have \<open>OK (Dis A B) G\<close>
      using * Assume by simp

    { assume \<open>(\<forall>G'. set G' = S \<union> {A} \<longrightarrow> OK Falsity G')\<close>
        and \<open>(\<forall>G'. set G' = S \<union> {B} \<longrightarrow> OK Falsity G')\<close>
      then have \<open>OK Falsity (A # G)\<close> and \<open>OK Falsity (B # G)\<close>
        using * by simp_all
      then have \<open>OK Falsity G\<close>
        using Dis_E \<open>OK (Dis A B) G\<close> by blast
      then have False
        using \<open>\<not> (OK Falsity G)\<close> by blast }
    then show \<open>S \<union> {A} \<in> ?C \<or> S \<union> {B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Neg (Con A B) \<in> S\<close>

    let ?x = \<open>Dis (Neg A) (Neg B)\<close>

    have \<open>OK A (B # A # Neg ?x # G)\<close> and \<open>OK B (B # A # Neg ?x # G)\<close>
      using Assume by simp_all
    then have \<open>OK (Con A B) (B # A # Neg ?x # G)\<close>
      using Con_I by blast
    moreover have \<open>OK (Neg (Con A B)) (B # A # Neg ?x # G)\<close>
      using * \<open>Neg (Con A B) \<in> S\<close> Assume by simp
    ultimately have \<open>OK Falsity (B # A # Neg ?x # G)\<close>
      using Imp_E by blast
    then have \<open>OK (Neg B) (A # Neg ?x # G)\<close>
      using Imp_I by blast
    then have \<open>OK ?x (A # Neg ?x # G)\<close>
      using Dis_I2 by blast
    moreover have \<open>OK (Neg ?x) (A # Neg ?x # G)\<close>
      using Assume by simp
    ultimately have \<open>OK Falsity (A # Neg ?x # G)\<close>
      using Imp_E by blast
    then have \<open>OK (Neg A) (Neg ?x # G)\<close>
      using Imp_I by blast
    then have \<open>OK ?x (Neg ?x # G)\<close>
      using Dis_I1 by blast
    then have \<open>OK (Dis (Neg A) (Neg B)) G\<close>
      using Boole' by blast

    { assume \<open>(\<forall>G'. set G' = S \<union> {Neg A} \<longrightarrow> OK Falsity G')\<close>
        and \<open>(\<forall>G'. set G' = S \<union> {Neg B} \<longrightarrow> OK Falsity G')\<close>
      then have \<open>OK Falsity (Neg A # G )\<close> and \<open>OK Falsity (Neg B # G)\<close>
        using * by simp_all
      then have \<open>OK Falsity G\<close>
        using Dis_E \<open>OK (Dis (Neg A) (Neg B)) G\<close> by blast
      then have False
        using \<open>\<not> (OK Falsity G)\<close> by blast }
    then show \<open>S \<union> {Neg A} \<in> ?C \<or> S \<union> {Neg B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Imp A B \<in> S\<close>

    let ?x = \<open>Dis (Neg A) B\<close>

    have \<open>OK A (A # Neg ?x # G)\<close>
      using Assume by simp
    moreover have \<open>OK (Imp A B) (A # Neg ?x # G)\<close>
      using * \<open>Imp A B \<in> S\<close> Assume by simp
    ultimately have \<open>OK B (A # Neg ?x # G)\<close>
      using Imp_E by blast
    then have \<open>OK ?x (A # Neg ?x # G)\<close>
      using Dis_I2 by blast
    moreover have \<open>OK (Neg ?x) (A # Neg ?x # G)\<close>
      using Assume by simp
    ultimately have \<open>OK Falsity (A # Neg ?x # G)\<close>
      using Imp_E by blast
    then have \<open>OK (Neg A) (Neg ?x # G)\<close>
      using Imp_I by blast
    then have \<open>OK ?x (Neg ?x # G)\<close>
      using Dis_I1 by blast
    then have \<open>OK (Dis (Neg A) B) G\<close>
      using Boole' by blast

    { assume \<open>(\<forall>G'. set G' = S \<union> {Neg A} \<longrightarrow> OK Falsity G')\<close>
        and \<open>(\<forall>G'. set G' = S \<union> {B} \<longrightarrow> OK Falsity G')\<close>
      then have \<open>OK Falsity (Neg A # G)\<close> and \<open>OK Falsity (B # G)\<close>
        using * by simp_all
      then have \<open>OK Falsity G\<close>
        using Dis_E \<open>OK (Dis (Neg A) B) G\<close> by blast
      then have False
        using \<open>\<not> (OK Falsity G)\<close> by blast }
    then show \<open>S \<union> {Neg A} \<in> ?C \<or> S \<union> {B} \<in> ?C\<close>
      by blast }

  { fix P t
    assume \<open>closed_term 0 t\<close> and \<open>Uni P \<in> S\<close>
    then have \<open>OK (Uni P) G\<close>
      using Assume * by simp
    then have \<open>OK (sub 0 t P) G\<close>
      using Uni_E by blast

    { assume \<open>OK Falsity (sub 0 t P # G)\<close>
      then have \<open>OK Falsity G\<close>
        using cut \<open>OK (sub 0 t P) G\<close> by blast
      then have False
        using \<open>\<not> (OK Falsity G)\<close> by blast }
    then have \<open>\<not> (OK Falsity (sub 0 t P # G))\<close>
      by blast
    moreover have \<open>S \<union> {sub 0 t P} = set (sub 0 t P # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {sub 0 t P} \<in> ?C\<close>
      by blast }

  { fix P t
    assume \<open>closed_term 0 t\<close> and \<open>Neg (Exi P) \<in> S\<close>
    then have \<open>OK (Neg (Exi P)) G\<close>
      using Assume * by simp
    then have \<open>OK (sub 0 t P) (sub 0 t P # G)\<close>
      using Assume by simp
    then have \<open>OK (Exi P) (sub 0 t P # G)\<close>
      using Exi_I by blast
    moreover have \<open>OK (Neg (Exi P)) (sub 0 t P # G)\<close>
      using * \<open>Neg (Exi P) \<in> S\<close> Assume by simp
    ultimately have \<open>OK Falsity (sub 0 t P # G)\<close>
      using Imp_E by blast
    then have \<open>OK (Neg (sub 0 t P)) G\<close>
      using Imp_I by blast

    { assume \<open>OK Falsity (Neg (sub 0 t P) # G)\<close>
      then have \<open>OK Falsity G\<close>
        using cut \<open>OK (Neg (sub 0 t P)) G\<close> by blast
      then have False
        using \<open>\<not> (OK Falsity G)\<close> by blast }
    then have \<open>\<not> (OK Falsity (Neg (sub 0 t P) # G))\<close>
      by blast
    moreover have \<open>S \<union> {Neg (sub 0 t P)} = set (Neg (sub 0 t P) # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {Neg (sub 0 t P)} \<in> ?C\<close>
      by blast }

  { fix P
    assume \<open>Exi P \<in> S\<close>
    then have \<open>OK (Exi P) G\<close>
      using * Assume by simp

    have \<open>finite ((\<Union>p \<in> set G. params p) \<union> params P)\<close>
      by simp
    then have \<open>infinite (- ((\<Union>p \<in> set G. params p) \<union> params P))\<close>
      using infinite_UNIV_listI Diff_infinite_finite finite_compl by blast
    then have \<open>infinite (- ((\<Union>p \<in> set G. params p) \<union> params P))\<close>
      by (simp add: Compl_eq_Diff_UNIV)
    then obtain x where **: \<open>x \<in> - ((\<Union>p \<in> set G. params p) \<union> params P)\<close>
      using infinite_imp_nonempty by blast

    { assume \<open>OK Falsity (sub 0 (Fun x []) P # G)\<close>
      moreover have \<open>news x (P # Falsity # G)\<close>
        using ** by (simp add: list_all_iff)
      ultimately have \<open>OK Falsity G\<close>
        using Exi_E \<open>OK (Exi P) G\<close> by fast
      then have False
        using \<open>\<not> (OK Falsity G)\<close> by blast}
    then have \<open>\<not> (OK Falsity (sub 0 (Fun x []) P # G))\<close>
      by blast
    moreover have \<open>S \<union> {sub 0 (Fun x []) P} = set (sub 0 (Fun x []) P # G)\<close>
      using * by simp
    ultimately show \<open>\<exists>x. S \<union> {sub 0 (Fun x []) P} \<in> ?C\<close>
      by blast }

  { fix P
    assume \<open>Neg (Uni P) \<in> S\<close>
    then have \<open>OK (Neg (Uni P)) G\<close>
      using * Assume by simp

    have \<open>finite ((\<Union>p \<in> set G. params p) \<union> params P)\<close>
      by simp
    then have \<open>infinite (- ((\<Union>p \<in> set G. params p) \<union> params P))\<close>
      using infinite_UNIV_listI Diff_infinite_finite finite_compl by blast
    then have \<open>infinite (- ((\<Union>p \<in> set G. params p) \<union> params P))\<close>
      by (simp add: Compl_eq_Diff_UNIV)
    then obtain x where **: \<open>x \<in> - ((\<Union>p \<in> set G. params p) \<union> params P)\<close>
      using infinite_imp_nonempty by blast

    let ?x = \<open>Neg (Exi (Neg P))\<close>

    have \<open>OK (Neg (sub 0 (Fun x []) P)) (Neg (sub 0 (Fun x []) P) # ?x # G)\<close>
      using Assume by simp
    then have \<open>OK (Exi (Neg P)) (Neg (sub 0 (Fun x []) P) # ?x # G)\<close>
      using Exi_I by simp
    moreover have \<open>OK ?x (Neg (sub 0 (Fun x []) P) # ?x # G)\<close>
      using Assume by simp
    ultimately have \<open>OK Falsity (Neg (sub 0 (Fun x []) P) # ?x # G)\<close>
      using Imp_E by blast
    then have \<open>OK (sub 0 (Fun x []) P) (?x # G)\<close>
      using Boole by blast
    moreover have \<open>news x (P # ?x # G)\<close>
      using ** by (simp add: list_all_iff)
    ultimately have \<open>OK (Uni P) (?x # G)\<close>
      using Uni_I by fast
    moreover have \<open>OK (Neg (Uni P)) (?x # G)\<close>
      using * \<open>Neg (Uni P) \<in> S\<close> Assume by simp
    ultimately have \<open>OK Falsity (?x # G)\<close>
      using Imp_E by blast
    then have \<open>OK (Exi (Neg P)) G\<close>
      using Boole by blast

    { assume \<open>OK Falsity (Neg (sub 0 (Fun x []) P) # G)\<close>
      then have \<open>OK (sub 0 (Fun x []) P) G\<close>
        using Boole by blast
      moreover have \<open>news x (P # G)\<close>
        using ** by (simp add: list_all_iff)
      ultimately have \<open>OK (Uni P) G\<close>
        using Uni_I by blast
      then have \<open>OK Falsity G\<close>
        using Imp_E \<open>OK (Neg (Uni P)) G\<close> by blast
      then have False
        using \<open>\<not> (OK Falsity G)\<close> by blast }
    then have \<open>\<not> (OK Falsity (Neg (sub 0 (Fun x []) P) # G))\<close>
      by blast
    moreover have \<open>S \<union> {Neg (sub 0 (Fun x []) P)} = set (Neg (sub 0 (Fun x []) P) # G)\<close>
      using * by simp
    ultimately show \<open>\<exists>x. S \<union> {Neg (sub 0 (Fun x []) P)} \<in> ?C\<close>
      by blast }
qed

theorem natded_complete:
  assumes \<open>closed 0 p\<close> and \<open>list_all (closed 0) z\<close>
    and mod: \<open>\<forall>(e :: nat \<Rightarrow> htm) f g. list_all (semantics e f g) z \<longrightarrow> semantics e f g p\<close>
  shows \<open>OK p z\<close>
proof (rule Boole, rule ccontr)
  fix e
  assume \<open>\<not> (OK Falsity (Neg p # z))\<close>

  let ?S = \<open>set (Neg p # z)\<close>
  let ?C = \<open>{set G | G. \<not> (OK Falsity G)}\<close>
  let ?C' = \<open>mk_finite_char (mk_alt_consistency (close ?C))\<close>
  let ?H = \<open>Extend ?S ?C' from_nat\<close>
  let ?f = HFun
  let ?g = \<open>\<lambda>i l. Pre i (tms_of_htms l) \<in> ?H\<close>

  { fix x
    assume \<open>x \<in> ?S\<close>
    moreover have \<open>closed 0 x\<close>
      using \<open>closed 0 p\<close> \<open>list_all (closed 0) z\<close> \<open>x \<in> ?S\<close>
      by (auto simp: list_all_iff)
    moreover have \<open>?S \<in> ?C\<close>
      using \<open>\<not> (OK Falsity (Neg p # z))\<close> by blast
    moreover have \<open>consistency ?C\<close>
      using OK_consistency by blast
    moreover have \<open>infinite (- (\<Union>p \<in> ?S. params p))\<close>
      by (simp add: Compl_eq_Diff_UNIV infinite_UNIV_listI)
    ultimately have \<open>semantics e ?f ?g x\<close>
      using model_existence by simp }
  then have \<open>semantics e ?f ?g (Neg p)\<close>
    and \<open>list_all (semantics e ?f ?g) z\<close>
    unfolding list_all_def by fastforce+
  then have \<open>semantics e ?f ?g p\<close>
    using mod by blast
  then show False
    using \<open>semantics e ?f ?g (Neg p)\<close> by simp
qed

subsection \<open>Löwenheim-Skolem\<close>

theorem sat_consistency:
  \<open>consistency {S. infinite (- (\<Union>p \<in> S. params p)) \<and> (\<exists>f. \<forall>p \<in> S. semantics e f g p)}\<close>
  (is \<open>consistency ?C\<close>)
  unfolding consistency_def
proof (intro allI impI conjI)
  fix S :: \<open>fm set\<close>
  assume \<open>S \<in> ?C\<close>
  then have inf_params: \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
    and \<open>\<exists>f. \<forall>p \<in> S. semantics e f g p\<close>
    by blast+
  then obtain f where *: \<open>\<forall>x \<in> S. semantics e f g x\<close> by blast

  { fix p ts
    show \<open>\<not> (Pre p ts \<in> S \<and> Neg (Pre p ts) \<in> S)\<close>
    proof
      assume \<open>Pre p ts \<in> S \<and> Neg (Pre p ts) \<in> S\<close>
      then have \<open>semantics e f g (Pre p ts) \<and> semantics e f g (Neg (Pre p ts))\<close>
        using * by blast
      then show False by auto
    qed }

  show \<open>Falsity \<notin> S\<close>
    using * by fastforce

  { fix Z
    assume \<open>Neg (Neg Z) \<in> S\<close>
    then have \<open>\<forall>x \<in> S \<union> {Z}. semantics e f g x\<close>
      using * by auto
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {Z}. params p))\<close>
      using inf_params by (simp add: set_inter_compl_diff)
    ultimately show \<open>S \<union> {Z} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Con A B \<in> S\<close>
    then have \<open>\<forall>x \<in> S \<union> {A, B}. semantics e f g x\<close>
      using * by auto
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {A, B}. params p))\<close>
      using inf_params by (simp add: set_inter_compl_diff)
    ultimately show \<open>S \<union> {A, B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Neg (Dis A B) \<in> S\<close>
    then have \<open>\<forall>x \<in> S \<union> {Neg A, Neg B}. semantics e f g x\<close>
      using * by auto
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {Neg A, Neg B}. params p))\<close>
      using inf_params by (simp add: set_inter_compl_diff)
    ultimately show \<open>S \<union> {Neg A, Neg B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Neg (Imp A B) \<in> S\<close>
    then have \<open>\<forall>x \<in> S \<union> {A, Neg B}. semantics e f g x\<close>
      using * by auto
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {A, Neg B}. params p))\<close>
      using inf_params by (simp add: set_inter_compl_diff)
    ultimately show \<open>S \<union> {A, Neg B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Dis A B \<in> S\<close>
    then have \<open>(\<forall>x \<in> S \<union> {A}. semantics e f g x) \<or>
               (\<forall>x \<in> S \<union> {B}. semantics e f g x)\<close>
      using * by auto
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {A}. params p))\<close>
      and \<open>infinite (- (\<Union>p \<in> S \<union> {B}. params p))\<close>
      using inf_params by (simp_all add: set_inter_compl_diff)
    ultimately show \<open>S \<union> {A} \<in> ?C \<or> S \<union> {B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Neg (Con A B) \<in> S\<close>
    then have \<open>(\<forall>x \<in> S \<union> {Neg A}. semantics e f g x) \<or>
               (\<forall>x \<in> S \<union> {Neg B}. semantics e f g x)\<close>
      using * by auto
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {Neg A}. params p))\<close>
      and \<open>infinite (- (\<Union>p \<in> S \<union> {Neg B}. params p))\<close>
      using inf_params by (simp_all add: set_inter_compl_diff)
    ultimately show \<open>S \<union> {Neg A} \<in> ?C \<or> S \<union> {Neg B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Imp A B \<in> S\<close>
    then have \<open>(\<forall>x \<in> S \<union> {Neg A}. semantics e f g x) \<or>
               (\<forall>x \<in> S \<union> {B}. semantics e f g x)\<close>
      using * by auto
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {Neg A}. params p))\<close>
      and \<open>infinite (- (\<Union>p \<in> S \<union> {B}. params p))\<close>
      using inf_params by (simp_all add: set_inter_compl_diff)
    ultimately show \<open>S \<union> {Neg A} \<in> ?C \<or> S \<union> {B} \<in> ?C\<close>
      by blast }

  { fix P t
    assume \<open>Uni P \<in> S\<close>
    then have \<open>\<forall>x \<in> S \<union> {sub 0 t P}. semantics e f g x\<close>
      using * by auto
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {sub 0 t P}. params p))\<close>
      using inf_params by (simp add: set_inter_compl_diff)
    ultimately show \<open>S \<union> {sub 0 t P} \<in> ?C\<close>
      by blast }

  { fix P t
    assume \<open>Neg (Exi P) \<in> S\<close>
    then have \<open>\<forall>x \<in> S \<union> {Neg (sub 0 t P)}. semantics e f g x\<close>
      using * by auto
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {Neg (sub 0 t P)}. params p))\<close>
      using inf_params by (simp add: set_inter_compl_diff)
    ultimately show \<open>S \<union> {Neg (sub 0 t P)} \<in> ?C\<close>
      by blast }

  { fix P
    assume \<open>Exi P \<in> S\<close>
    then obtain y where \<open>semantics (put e 0 y) f g P\<close>
      using * by fastforce
    moreover obtain x where **: \<open>x \<in> - (\<Union>p \<in> S. params p)\<close>
      using inf_params infinite_imp_nonempty by blast
    then have \<open>x \<notin> params P\<close>
      using \<open>Exi P \<in> S\<close> by auto
    moreover have \<open>\<forall>p \<in> S. semantics e (f(x := \<lambda>_. y)) g p\<close>
      using * ** by simp
    ultimately have \<open>\<forall>p \<in> S \<union> {sub 0 (Fun x []) P}.
        semantics e (f(x := \<lambda>_. y)) g p\<close>
      by simp
    moreover have
      \<open>infinite (- (\<Union>p \<in> S \<union> {sub 0 (Fun x []) P}. params p))\<close>
      using inf_params by (simp add: set_inter_compl_diff)
    ultimately show \<open>\<exists>x. S \<union> {sub 0 (Fun x []) P} \<in> ?C\<close>
      by blast }

  { fix P
    assume \<open>Neg (Uni P) \<in> S\<close>
    then obtain y where \<open>\<not> semantics (put e 0 y) f g P\<close>
      using * by fastforce
    moreover obtain x where **: \<open>x \<in> - (\<Union>p \<in> S. params p)\<close>
      using inf_params infinite_imp_nonempty by blast
    then have \<open>x \<notin> params P\<close>
      using \<open>Neg (Uni P) \<in> S\<close> by auto
    moreover have \<open>\<forall>p \<in> S. semantics e (f(x := \<lambda>_. y)) g p\<close>
      using * ** by simp
    ultimately have \<open>\<forall>p \<in> S \<union> {Neg (sub 0 (Fun x []) P)}. semantics e (f(x := \<lambda>_. y)) g p\<close>
      by simp
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {Neg (sub 0 (Fun x []) P)}. params p))\<close>
      using inf_params by (simp add: set_inter_compl_diff)
    ultimately show \<open>\<exists>x. S \<union> {Neg (sub 0 (Fun x []) P)} \<in> ?C\<close>
      by blast }
qed

primrec double :: \<open>'a list \<Rightarrow> 'a list\<close> where
  \<open>double [] = []\<close> |
  \<open>double (x#xs) = x # x # double xs\<close>

fun undouble :: \<open>'a list \<Rightarrow> 'a list\<close> where
  \<open>undouble [] = []\<close> |
  \<open>undouble [x] = [x]\<close> |
  \<open>undouble (x#_#xs) = x # undouble xs\<close>

lemma undouble_double_id [simp]: \<open>undouble (double xs) = xs\<close>
  by (induct xs) simp_all

lemma infinite_double_Cons: \<open>infinite (range (\<lambda>xs. a # double xs))\<close>
  using undouble_double_id infinite_UNIV_listI
  by (metis (mono_tags, lifting) finite_imageD inj_onI list.inject)

lemma double_Cons_neq: \<open>a # (double xs) \<noteq> double ys\<close>
proof -
  have \<open>odd (length (a # double xs))\<close>
    by (induct xs) simp_all
  moreover have \<open>even (length (double ys))\<close>
    by (induct ys) simp_all
  ultimately show ?thesis
    by fastforce
qed

lemma doublep_infinite_params: \<open>infinite (- (\<Union>p \<in> psubst double ` S. params p))\<close>
proof (rule infinite_super)
  fix a
  show \<open>infinite (range (\<lambda>xs :: id. a # double xs))\<close>
    using infinite_double_Cons by metis
next
  fix a
  show \<open>range (\<lambda>xs. a # double xs) \<subseteq> - (\<Union>p \<in> psubst double ` S. params p)\<close>
    using double_Cons_neq by fastforce
qed

theorem loewenheim_skolem:
  assumes \<open>\<forall>p \<in> S. semantics e f g p\<close> \<open>\<forall>p \<in> S. closed 0 p\<close>
  defines \<open>C \<equiv> {S. infinite (- (\<Union>p \<in> S. params p)) \<and> (\<exists>f. \<forall>p \<in> S. semantics e f g p)}\<close>
  defines \<open>C' \<equiv> mk_finite_char (mk_alt_consistency (close C))\<close>
  defines \<open>H \<equiv> Extend (psubst double ` S) C' from_nat\<close>
  shows \<open>\<forall>p \<in> S. semantics e' (\<lambda>xs. HFun (double xs)) (\<lambda>i l. Pre i (tms_of_htms l) \<in> H) p\<close>
proof (intro ballI impI)
  fix p
  assume \<open>p \<in> S\<close>

  let ?g = \<open>\<lambda>i l. Pre i (tms_of_htms l) \<in> H\<close>

  have \<open>\<forall>p \<in> psubst double ` S. semantics e (\<lambda>xs. f (undouble xs)) g p\<close>
    using \<open>\<forall>p \<in> S. semantics e f g p\<close> by (simp add: psubst_semantics)
  then have \<open>psubst double ` S \<in> C\<close>
    using C_def doublep_infinite_params by blast
  moreover have \<open>psubst double p \<in> psubst double ` S\<close>
    using \<open>p \<in> S\<close> by blast
  moreover have \<open>closed 0 (psubst double p)\<close>
    using \<open>\<forall>p \<in> S. closed 0 p\<close> \<open>p \<in> S\<close> by simp
  moreover have \<open>consistency C\<close>
    using C_def sat_consistency by blast
  ultimately have \<open>semantics e' HFun ?g (psubst double p)\<close>
    using C_def C'_def H_def model_existence by simp
  then show \<open>semantics e' (\<lambda>xs. HFun (double xs)) ?g p\<close>
    using psubst_semantics by blast
qed

subsection \<open>Countable variants\<close>

lemma infinity:
  assumes inj: \<open>\<forall>n :: nat. undiago (diago n) = n\<close>
  assumes all_tree: \<open>\<forall>n :: nat. (diago n) \<in> tree\<close>
  shows \<open>infinite tree\<close>
proof -
  from inj all_tree have \<open>\<forall>n. n = undiago (diago n) \<and> (diago n) \<in> tree\<close>
    by simp
  then have \<open>undiago ` tree = (UNIV :: nat set)\<close>
    by auto
  then have \<open>infinite tree\<close>
    by (metis finite_imageI infinite_UNIV_nat)
  then show ?thesis
    by simp
qed

definition nat_of_string :: \<open>string \<Rightarrow> nat\<close> where
  \<open>nat_of_string \<equiv> (SOME f. bij f)\<close>

definition string_of_nat :: \<open>nat \<Rightarrow> string\<close> where
  \<open>string_of_nat \<equiv> inv nat_of_string\<close>

lemma nat_of_string_string_of_nat [simp]: \<open>nat_of_string (string_of_nat n) = n\<close>
  using Schroeder_Bernstein bij_is_surj infinite_UNIV_listI infinite_iff_countable_subset
    nat_of_string_def someI_ex string_of_nat_def surj_f_inv_f top_greatest inj_undiag_string
  by (metis (mono_tags, lifting))

lemma string_of_nat_nat_of_string [simp]: \<open>string_of_nat (nat_of_string n) = n\<close>
  using Schroeder_Bernstein UNIV_I bij_is_inj infinite_UNIV_listI infinite_iff_countable_subset
    inv_into_f_f nat_of_string_def someI_ex string_of_nat_def top_greatest inj_undiag_string
  by (metis (mono_tags, lifting))

lemma infinite_htms: \<open>infinite (UNIV :: htm set)\<close>
proof -
  let ?diago = \<open>\<lambda>n. HFun (string_of_nat n) []\<close>
  let ?undiago = \<open>\<lambda>a. nat_of_string (case a of HFun f ts \<Rightarrow> f)\<close>
  show ?thesis
    using infinity[of ?undiago ?diago UNIV] by simp
qed

definition e_conv :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'b)\<close> where
  \<open>e_conv b_of_a e \<equiv> (\<lambda>n. b_of_a (e n))\<close>

definition f_conv ::
  \<open>('a \<Rightarrow> 'b) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'b list \<Rightarrow> 'b)\<close> where
  \<open>f_conv b_of_a f \<equiv> (\<lambda>a ts. b_of_a (f a (map (inv b_of_a) ts)))\<close>

definition g_conv ::
  \<open>('a \<Rightarrow> 'b) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> (id \<Rightarrow> 'b list \<Rightarrow> bool)\<close> where
  \<open>g_conv b_of_a g \<equiv> (\<lambda>a ts. g a (map (inv b_of_a) ts))\<close>

lemma semantics_bij':
  assumes \<open>bij (b_of_a :: 'a \<Rightarrow> 'b)\<close>
  shows
    \<open>semantics_term (e_conv b_of_a e) (f_conv b_of_a f) p = b_of_a (semantics_term e f p)\<close>
    \<open>semantics_list (e_conv b_of_a e) (f_conv b_of_a f) l = map b_of_a (semantics_list e f l)\<close>
  unfolding e_conv_def f_conv_def using assms
  by (induct p and l rule: semantics_term.induct semantics_list.induct) (simp_all add: bij_is_inj)

lemma put_e_conv: \<open>(put (e_conv b_of_a e) m (b_of_a x)) = e_conv b_of_a (put e m x)\<close>
  unfolding e_conv_def by auto

lemma semantics_bij:
  assumes \<open>bij (b_of_a :: 'a \<Rightarrow> 'b)\<close>
  shows \<open>semantics e f g p = semantics (e_conv b_of_a e) (f_conv b_of_a f) (g_conv b_of_a g) p\<close>
proof (induct p arbitrary: e f g)
  case (Pre a l)
  then show ?case
    unfolding g_conv_def using assms
    by (simp add: semantics_bij' bij_is_inj)
next
  case (Exi p)
  let ?e = \<open>e_conv b_of_a e\<close>
    and ?f = \<open>f_conv b_of_a f\<close>
    and ?g = \<open>g_conv b_of_a g\<close>

  have \<open>(\<exists>x'. semantics (put ?e 0 x') ?f ?g p) = (\<exists>x. semantics (put ?e 0 (b_of_a x)) ?f ?g p)\<close>
    using assms by (metis bij_pointE)
  also have \<open>\<dots> = (\<exists>x. semantics (e_conv b_of_a (put e 0 x)) ?f ?g p)\<close>
    using put_e_conv by metis
  finally show ?case
    using Exi by simp
next
  case (Uni p)
  have \<open>(\<forall>x. semantics (put (e_conv b_of_a e) 0 x) (f_conv b_of_a f) (g_conv b_of_a g) p) =
        (\<forall>x. semantics (put (e_conv b_of_a e) 0 (b_of_a x)) (f_conv b_of_a f) (g_conv b_of_a g) p)\<close>
    using assms by (metis bij_pointE)
  also have \<open>\<dots> = (\<forall>x. semantics (e_conv b_of_a (put e 0 x)) (f_conv b_of_a f) (g_conv b_of_a g) p)\<close>
    using put_e_conv by metis
  finally show ?case
    using Uni by simp
qed simp_all

fun
  hterm_of_btree :: \<open>btree \<Rightarrow> htm\<close> and
  hterm_list_of_btree :: \<open>btree \<Rightarrow> htm list\<close> where
  \<open>hterm_of_btree (Leaf _) = undefined\<close>
| \<open>hterm_of_btree (Branch (Leaf m) t) =
     HFun (diag_string m) (hterm_list_of_btree t)\<close>
| \<open>hterm_list_of_btree (Leaf m) = []\<close>
| \<open>hterm_list_of_btree (Branch t1 t2) =
     hterm_of_btree t1 # hterm_list_of_btree t2\<close>
| \<open>hterm_of_btree (Branch (Branch _ _) _) = undefined\<close>

primrec
  btree_of_hterm :: \<open>htm \<Rightarrow> btree\<close> and
  btree_of_hterm_list :: \<open>htm list \<Rightarrow> btree\<close> where
  \<open>btree_of_hterm (HFun m ts) = Branch (Leaf (undiag_string m)) (btree_of_hterm_list ts)\<close>
| \<open>btree_of_hterm_list [] = Leaf 0\<close>
| \<open>btree_of_hterm_list (t # ts) = Branch (btree_of_hterm t) (btree_of_hterm_list ts)\<close>

theorem hterm_btree:
  shows \<open>hterm_of_btree (btree_of_hterm t) = t\<close>
    and \<open>hterm_list_of_btree (btree_of_hterm_list ts) = ts\<close>
  by (induct t and ts rule: btree_of_hterm.induct btree_of_hterm_list.induct) simp_all

definition diag_hterm :: \<open>nat \<Rightarrow> htm\<close> where
  \<open>diag_hterm n = hterm_of_btree (diag_btree n)\<close>

definition undiag_hterm :: \<open>htm \<Rightarrow> nat\<close> where
  \<open>undiag_hterm t = undiag_btree (btree_of_hterm t)\<close>

theorem diag_undiag_hterm [simp]: \<open>diag_hterm (undiag_hterm t) = t\<close>
  by (simp add: diag_hterm_def undiag_hterm_def hterm_btree)

lemma htm: \<open>\<exists>f :: htm \<Rightarrow> nat. inj f\<close>
  unfolding inj_def using diag_undiag_hterm by metis

definition denumerable :: \<open>'a set \<Rightarrow> bool\<close>
  where \<open>denumerable S \<equiv> (\<exists>f :: 'a \<Rightarrow> nat. inj_on f S) \<and> (\<exists>f :: nat \<Rightarrow> 'a. range f \<subseteq> S \<and> inj f)\<close>

lemma denumerable_bij: \<open>denumerable S \<longleftrightarrow> (\<exists>f. bij_betw f (UNIV :: nat set) S)\<close>
  unfolding denumerable_def
  using Schroeder_Bernstein UNIV_I bij_betw_def bij_betw_inv subsetI by metis

hide_fact denumerable_def

abbreviation \<open>sentence \<equiv> closed 0\<close>

lemma sentence_completeness':
  assumes \<open>\<forall>(e :: nat \<Rightarrow> 'a) f g. list_all (semantics e f g) z \<longrightarrow> semantics e f g p\<close>
    and \<open>sentence p\<close>
    and \<open>list_all sentence z\<close>
    and \<open>denumerable (UNIV :: 'a set)\<close>
  shows \<open>OK p z\<close>
proof -
  have \<open>\<forall>(e :: nat \<Rightarrow> htm) f g.
    list_all (semantics e f g) z \<longrightarrow> semantics e f g p\<close>
  proof (intro allI)
    fix e :: \<open>nat \<Rightarrow> htm\<close>
      and f :: \<open>id \<Rightarrow> htm list \<Rightarrow> htm\<close>
      and g :: \<open>id \<Rightarrow> htm list \<Rightarrow> bool\<close>

    obtain a_of_htm :: \<open>htm \<Rightarrow> 'a\<close> where p_a_of_hterm: \<open>bij a_of_htm\<close>
      using assms(4) infinite_htms htm denumerable_bij
        Schroeder_Bernstein bij_comp infinite_iff_countable_subset top_greatest by metis

    let ?e = \<open>e_conv a_of_htm e\<close>
    let ?f = \<open>f_conv a_of_htm f\<close>
    let ?g = \<open>g_conv a_of_htm g\<close>

    have \<open>list_all (semantics ?e ?f ?g) z \<longrightarrow> semantics ?e ?f ?g p\<close>
      using assms(1) by blast
    then show \<open>list_all (semantics e f g) z \<longrightarrow> semantics e f g p\<close>
      using p_a_of_hterm semantics_bij by (metis list.pred_cong)
  qed
  then show ?thesis
    using assms(2) assms(3) natded_complete by blast
qed

theorem sentence_completeness:
  assumes \<open>\<forall>(e :: nat \<Rightarrow> 'a) f g. semantics e f g p\<close>
    and \<open>sentence p\<close>
    and \<open>denumerable (UNIV :: 'a set)\<close>
  shows \<open>OK p []\<close>
  using assms by (simp add: sentence_completeness')

corollary \<open>\<forall>(e :: nat \<Rightarrow> nat) f g. semantics e f g p \<Longrightarrow> sentence p \<Longrightarrow> OK p []\<close>
  using sentence_completeness denumerable_bij by blast

section \<open>Completeness for Open Formulas\<close>

subsection \<open>Renaming\<close>

lemma new_psubst_image':
  \<open>new_term c t \<Longrightarrow> d \<notin> image f (params_term t) \<Longrightarrow> new_term d (psubst_term (f(c := d)) t)\<close>
  \<open>new_list c l \<Longrightarrow> d \<notin> image f (params_list l) \<Longrightarrow> new_list d (psubst_list (f(c := d)) l)\<close>
  by (induct t and l rule: new_term.induct new_list.induct) auto

lemma new_psubst_image: \<open>new c p \<Longrightarrow> d \<notin> image f (params p) \<Longrightarrow> new d (psubst (f(c := d)) p)\<close>
  using new_psubst_image' by (induct p) auto

lemma news_psubst: \<open>news c z \<Longrightarrow> d \<notin> image f (\<Union>p \<in> set z. params p) \<Longrightarrow>
    news d (map (psubst (f(c := d))) z)\<close>
  using new_psubst_image by (induct z) auto

lemma member_psubst: \<open>member p z \<Longrightarrow> member (psubst f p) (map (psubst f) z)\<close>
  by (induct z) auto

lemma OK_psubst: \<open>OK p z \<Longrightarrow> OK (psubst f p) (map (psubst f) z)\<close>
proof (induct p z arbitrary: f rule: OK.induct)
  case (Assume p z)
  then show ?case
    using OK.Assume member_psubst by blast
next
  case (Boole p z)
  then have \<open>OK Falsity (Neg (psubst f p) # map (psubst f) z)\<close>
    by simp
  then show ?case
    using OK.Boole by blast
next
  case (Imp_E p q z)
  then have \<open>OK (Imp (psubst f p) (psubst f q)) (map (psubst f) z)\<close>
    and \<open>OK (psubst f p) (map (psubst f) z)\<close>
    by simp_all
  then show ?case
    using OK.Imp_E by blast
next
  case (Imp_I q p z)
  then show ?case
    using OK.Imp_I by simp
next
  case (Dis_E p q z r)
  then have
    \<open>OK (Dis (psubst f p) (psubst f q)) (map (psubst f) z)\<close>
    \<open>OK (psubst f r) (psubst f p # map (psubst f) z)\<close>
    \<open>OK (psubst f r) (psubst f q # map (psubst f) z)\<close>
    by simp_all
  then show ?case
    using OK.Dis_E by blast
next
  case (Dis_I1 p z q)
  then show ?case
    using OK.Dis_I1 by simp
next
  case (Dis_I2 q z p)
  then show ?case
    using OK.Dis_I2 by simp
next
  case (Con_E1 p q z)
  then have \<open>OK (Con (psubst f p) (psubst f q)) (map (psubst f) z)\<close>
    by simp
  then show ?case
    using OK.Con_E1 by blast
next
  case (Con_E2 p q z)
  then have \<open>OK (Con (psubst f p) (psubst f q)) (map (psubst f) z)\<close>
    by simp
  then show ?case
    using OK.Con_E2 by blast
next
  case (Con_I p z q)
  then show ?case
    using OK.Con_I by simp
next
  case (Exi_E p z q c)
  let ?params = \<open>params p \<union> params q \<union> (\<Union>p \<in> set z. params p)\<close>

  have \<open>finite ?params\<close>
    by simp
  then obtain fresh where *: \<open>fresh \<notin> ?params \<union> {c} \<union> image f ?params\<close>
    using ex_new_if_finite
    by (metis finite.emptyI finite.insertI finite_UnI finite_imageI infinite_UNIV_listI)

  let ?f = \<open>f(c := fresh)\<close>

  have \<open>news c (p # q # z)\<close>
    using Exi_E by blast
  then have \<open>new fresh (psubst ?f p)\<close> \<open>new fresh (psubst ?f q)\<close> \<open>news fresh (map (psubst ?f) z)\<close>
    using * new_psubst_image news_psubst by (fastforce simp add: image_Un)+
  have \<open>OK (psubst ?f (Exi p)) (map (psubst ?f) z)\<close>
    using Exi_E by blast
  then have \<open>OK (Exi (psubst ?f p)) (map (psubst ?f) z)\<close>
    by simp
  moreover have \<open>OK (psubst ?f q) (map (psubst ?f) (sub 0 (Fun c []) p # z))\<close>
    using Exi_E by blast
  then have \<open>OK (psubst ?f q) (sub 0 (Fun fresh []) (psubst ?f p) # map (psubst ?f) z)\<close>
    by simp
  moreover have \<open>news fresh (map (psubst ?f) (p # q # z))\<close>
    using \<open>new fresh (psubst ?f p)\<close> \<open>new fresh (psubst ?f q)\<close> \<open>news fresh (map (psubst ?f) z)\<close>
    by simp
  then have \<open>news fresh (psubst ?f p # psubst ?f q # map (psubst ?f) z)\<close>
    by simp
  ultimately have \<open>OK (psubst ?f q) (map (psubst ?f) z)\<close>
    using OK.Exi_E by blast
  moreover have \<open>list_all (new c) z\<close>
    using Exi_E by simp
  then have \<open>map (psubst ?f) z = map (psubst f) z\<close>
    unfolding list_all_iff by simp
  ultimately show ?case
    using Exi_E by simp
next
  case (Exi_I t p z)
  then show ?case
    using OK.Exi_I by fastforce
next
  case (Uni_E p z t)
  then show ?case
    using OK.Uni_E by simp
next
  case (Uni_I c p z)
  let ?params = \<open>params p \<union>(\<Union>p \<in> set z. params p)\<close>

  have \<open>finite ?params\<close>
    by simp
  then obtain fresh where *: \<open>fresh \<notin> ?params \<union> {c} \<union> image f ?params\<close>
    using ex_new_if_finite
    by (metis finite.emptyI finite.insertI finite_UnI finite_imageI infinite_UNIV_listI)

  let ?f = \<open>f(c := fresh)\<close>

  have \<open>news c (p # z)\<close>
    using Uni_I by blast
  then have \<open>new fresh (psubst ?f p)\<close> \<open>news fresh (map (psubst ?f) z)\<close>
    using * new_psubst_image news_psubst by (fastforce simp add: image_Un)+
  then have \<open>map (psubst ?f) z = map (psubst f) z\<close>
    using Uni_I allnew new_params
    by (metis (mono_tags, lifting) Ball_set map_eq_conv news.simps(2) psubst_upd)

  have \<open>OK (psubst ?f (sub 0 (Fun c []) p)) (map (psubst ?f) z)\<close>
    using Uni_I by blast
  then have \<open>OK (sub 0 (Fun fresh []) (psubst ?f p)) (map (psubst ?f) z)\<close>
    by simp
  moreover have \<open>news fresh (map (psubst ?f) (p # z))\<close>
    using \<open>new fresh (psubst ?f p)\<close> \<open>news fresh (map (psubst ?f) z)\<close>
    by simp
  then have \<open>news fresh (psubst ?f p # map (psubst ?f) z)\<close>
    by simp
  ultimately have \<open>OK (Uni (psubst ?f p)) (map (psubst ?f) z)\<close>
    using OK.Uni_I by blast
  then show ?case
    using Uni_I \<open>map (psubst ?f) z = map (psubst f) z\<close> by simp
qed

subsection \<open>Substitution for constants\<close>

primrec
  subc_term :: \<open>id \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm\<close> and
  subc_list :: \<open>id \<Rightarrow> tm \<Rightarrow> tm list \<Rightarrow> tm list\<close> where
  \<open>subc_term c s (Var n) = Var n\<close> |
  \<open>subc_term c s (Fun i l) = (if i = c then s else Fun i (subc_list c s l))\<close> |
  \<open>subc_list c s [] = []\<close> |
  \<open>subc_list c s (t # l) = subc_term c s t # subc_list c s l\<close>

primrec subc :: \<open>id \<Rightarrow> tm \<Rightarrow> fm \<Rightarrow> fm\<close> where
  \<open>subc c s Falsity = Falsity\<close> |
  \<open>subc c s (Pre i l) = Pre i (subc_list c s l)\<close> |
  \<open>subc c s (Imp p q) = Imp (subc c s p) (subc c s q)\<close> |
  \<open>subc c s (Dis p q) = Dis (subc c s p) (subc c s q)\<close> |
  \<open>subc c s (Con p q) = Con (subc c s p) (subc c s q)\<close> |
  \<open>subc c s (Exi p) = Exi (subc c (inc_term s) p)\<close> |
  \<open>subc c s (Uni p) = Uni (subc c (inc_term s) p)\<close>

primrec subcs :: \<open>id \<Rightarrow> tm \<Rightarrow> fm list \<Rightarrow> fm list\<close> where
  \<open>subcs c s [] = []\<close> |
  \<open>subcs c s (p # z) = subc c s p # subcs c s z\<close>

lemma sub_0_inc:
  \<open>sub_term 0 s (inc_term t) = t\<close>
  \<open>sub_list 0 s (inc_list l) = l\<close>
  by (induct t and l rule: sub_term.induct sub_list.induct) simp_all

lemma sub_new':
  \<open>new_term c s \<Longrightarrow> new_term c t \<Longrightarrow> new_term c (sub_term m s t)\<close>
  \<open>new_term c s \<Longrightarrow> new_list c l \<Longrightarrow> new_list c (sub_list m s l)\<close>
  by (induct t and l rule: sub_term.induct sub_list.induct) simp_all

lemma sub_new: \<open>new_term c s \<Longrightarrow> new c p \<Longrightarrow> new c (sub m s p)\<close>
  using sub_new' by (induct p arbitrary: m s) simp_all

lemma sub_new_all:
  assumes \<open>a \<notin> set cs\<close> \<open>list_all (\<lambda>c. new c p) cs\<close>
  shows \<open>\<forall>c \<in> set cs. new c (sub m (Fun a []) p)\<close>
  using assms sub_new by (induct cs) auto

lemma subc_new' [simp]:
  \<open>new_term c t \<Longrightarrow> subc_term c s t = t\<close>
  \<open>new_list c l \<Longrightarrow> subc_list c s l = l\<close>
  by (induct t and l rule: new_term.induct new_list.induct) auto

lemma subc_new [simp]: \<open>new c p \<Longrightarrow> subc c s p = p\<close>
  by (induct p arbitrary: s) simp_all

lemma subcs_news [simp]: \<open>news c z \<Longrightarrow> subcs c s z = z\<close>
  by (induct z) simp_all

lemma subc_psubst' [simp]:
  \<open>(\<forall>x \<in> params_term t. x \<noteq> c \<longrightarrow> f x \<noteq> f c) \<Longrightarrow>
    psubst_term f (subc_term c s t) = subc_term (f c) (psubst_term f s) (psubst_term f t)\<close>
  \<open>(\<forall>x \<in> params_list l. x \<noteq> c \<longrightarrow> f x \<noteq> f c) \<Longrightarrow>
    psubst_list f (subc_list c s l) = subc_list (f c) (psubst_term f s) (psubst_list f l)\<close>
  by (induct t and l rule: psubst_term.induct psubst_list.induct) simp_all

lemma subc_psubst: \<open>(\<forall>x \<in> params p. x \<noteq> c \<longrightarrow> f x \<noteq> f c) \<Longrightarrow>
    psubst f (subc c s p) = subc (f c) (psubst_term f s) (psubst f p)\<close>
  by (induct p arbitrary: s) simp_all

lemma subcs_psubst: \<open>(\<forall>x \<in> (\<Union>p \<in> set z. params p). x \<noteq> c \<longrightarrow> f x \<noteq> f c) \<Longrightarrow>
    map (psubst f) (subcs c s z) = subcs (f c) (psubst_term f s) (map (psubst f) z)\<close>
  using subc_psubst by (induct z) simp_all

lemma new_inc':
  \<open>new_term c t \<Longrightarrow> new_term c (inc_term t)\<close>
  \<open>new_list c l \<Longrightarrow> new_list c (inc_list l)\<close>
  by (induct t and l rule: new_term.induct new_list.induct) simp_all

lemma new_subc':
  \<open>new_term d s \<Longrightarrow> new_term d t \<Longrightarrow> new_term d (subc_term c s t)\<close>
  \<open>new_term d s \<Longrightarrow> new_list d l \<Longrightarrow> new_list d (subc_list c s l)\<close>
  by (induct t and l rule: sub_term.induct sub_list.induct) simp_all

lemma new_subc: \<open>new_term d s \<Longrightarrow> new d p \<Longrightarrow> new d (subc c s p)\<close>
  using new_subc' by (induct p arbitrary: s) simp_all

lemma news_subcs: \<open>new_term d s \<Longrightarrow> news d z \<Longrightarrow> news d (subcs c s z)\<close>
  using new_subc by (induct z) simp_all

lemma psubst_new_free':
  \<open>c \<noteq> n \<Longrightarrow> new_term n (psubst_term (id(n := c)) t)\<close>
  \<open>c \<noteq> n \<Longrightarrow> new_list n (psubst_list (id(n := c)) l)\<close>
  by (induct t and l rule: params_term.induct params_list.induct) simp_all

lemma psubst_new_free: \<open>c \<noteq> n \<Longrightarrow> new n (psubst (id(n := c)) p)\<close>
  using psubst_new_free' by (induct p) simp_all

lemma map_psubst_new_free: \<open>c \<noteq> n \<Longrightarrow> news n (map (psubst (id(n := c))) z)\<close>
  using psubst_new_free by (induct z) simp_all

lemma psubst_new_away' [simp]:
  \<open>new_term fresh t \<Longrightarrow> psubst_term (id(fresh := c)) (psubst_term (id(c := fresh)) t) = t\<close>
  \<open>new_list fresh l \<Longrightarrow> psubst_list (id(fresh := c)) (psubst_list (id(c := fresh)) l) = l\<close>
  by (induct t and l rule: psubst_term.induct psubst_list.induct) auto

lemma psubst_new_away [simp]: \<open>new fresh p \<Longrightarrow> psubst (id(fresh := c)) (psubst (id(c := fresh)) p) = p\<close>
  by (induct p) simp_all

lemma map_psubst_new_away:
  \<open>news fresh z \<Longrightarrow> map (psubst (id(fresh := c))) (map (psubst (id(c := fresh))) z) = z\<close>
  by (induct z) simp_all

lemma psubst_new':
  \<open>new_term c t \<Longrightarrow> psubst_term (id(c := x)) t = t\<close>
  \<open>new_list c l \<Longrightarrow> psubst_list (id(c := x)) l = l\<close>
  by (induct t and l rule: psubst_term.induct psubst_list.induct) auto

lemma psubst_new: \<open>new c p \<Longrightarrow> psubst (id(c := x)) p = p\<close>
  using psubst_new' by (induct p) simp_all

lemma map_psubst_new: \<open>news c z \<Longrightarrow> map (psubst (id(c := x))) z = z\<close>
  using psubst_new by (induct z) simp_all

lemma inc_sub':
  \<open>inc_term (sub_term m u t) = sub_term (m + 1) (inc_term u) (inc_term t)\<close>
  \<open>inc_list (sub_list m u l) = sub_list (m + 1) (inc_term u) (inc_list l)\<close>
  by (induct t and l rule: sub_term.induct sub_list.induct) simp_all

lemma new_subc_same':
  \<open>new_term c s \<Longrightarrow> new_term c (subc_term c s t)\<close>
  \<open>new_term c s \<Longrightarrow> new_list c (subc_list c s l)\<close>
  by (induct t and l rule: subc_term.induct subc_list.induct) simp_all

lemma new_subc_same: \<open>new_term c s \<Longrightarrow> new c (subc c s p)\<close>
  using new_inc' new_subc_same' by (induct p arbitrary: s) simp_all

lemma inc_subc:
  \<open>inc_term (subc_term c s t) = subc_term c (inc_term s) (inc_term t)\<close>
  \<open>inc_list (subc_list c s l) = subc_list c (inc_term s) (inc_list l)\<close>
  by (induct t and l rule: inc_term.induct inc_list.induct) simp_all

lemma new_subc_put':
  \<open>new_term c s \<Longrightarrow> subc_term c s (sub_term m u t) = subc_term c s (sub_term m (subc_term c s u) t)\<close>
  \<open>new_term c s \<Longrightarrow> subc_list c s (sub_list m u l) = subc_list c s (sub_list m (subc_term c s u) l)\<close>
  using new_subc_same'
  by (induct t and l rule: subc_term.induct subc_list.induct) simp_all

lemma new_subc_put: \<open>new_term c s \<Longrightarrow> subc c s (sub m t p) = subc c s (sub m (subc_term c s t) p)\<close>
proof (induct p arbitrary: s m t)
  case Falsity
  show ?case
    by simp
next
  case (Pre i l)
  have \<open>subc_list c s (sub_list m t l) = subc_list c s (sub_list m (subc_term c s t) l)\<close>
    using Pre.prems new_subc_put'(2) by blast
  then show ?case
    by simp
next
  case (Imp p q)
  have \<open>subc c s (sub m t p) = subc c s (sub m (subc_term c s t) p)\<close>
    using Imp.hyps(1) Imp.prems by blast
  moreover have \<open>subc c s (sub m t q) = subc c s (sub m (subc_term c s t) q)\<close>
    using Imp.hyps(2) Imp.prems by blast
  ultimately show ?case
    by simp
next
  case (Dis p q)
  have \<open>subc c s (sub m t p) = subc c s (sub m (subc_term c s t) p)\<close>
    using Dis.hyps(1) Dis.prems by blast
  moreover have \<open>subc c s (sub m t q) = subc c s (sub m (subc_term c s t) q)\<close>
    using Dis.hyps(2) Dis.prems by blast
  ultimately show ?case
    by simp
next
  case (Con p q)
  have \<open>subc c s (sub m t p) = subc c s (sub m (subc_term c s t) p)\<close>
    using Con.hyps(1) Con.prems by blast
  moreover have \<open>subc c s (sub m t q) = subc c s (sub m (subc_term c s t) q)\<close>
    using Con.hyps(2) Con.prems by blast
  ultimately show ?case
    by simp
next
  case (Exi p)
  have \<open>subc c s (sub m (subc_term c s t) (Exi p)) =
      Exi (subc c (inc_term s) (sub (Suc m) (subc_term c (inc_term s) (inc_term t)) p))\<close>
    using inc_subc by simp
  also have \<open>\<dots> = Exi (subc c (inc_term s) (sub (Suc m) (inc_term t) p))\<close>
    using Exi new_inc' by metis
  finally show ?case
    by simp
next
  case (Uni p)
  have \<open>subc c s (sub m (subc_term c s t) (Uni p)) =
      Uni (subc c (inc_term s) (sub (Suc m) (subc_term c (inc_term s) (inc_term t)) p))\<close>
    using inc_subc by simp
  also have \<open>\<dots> = Uni (subc c (inc_term s) (sub (Suc m) (inc_term t) p))\<close>
    using Uni new_inc' by metis
  finally show ?case
    by simp
qed

lemma subc_sub_new':
  \<open>new_term c u \<Longrightarrow> subc_term c (sub_term m u s) (sub_term m u t) = sub_term m u (subc_term c s t)\<close>
  \<open>new_term c u \<Longrightarrow> subc_list c (sub_term m u s) (sub_list m u l) = sub_list m u (subc_list c s l)\<close>
  by (induct t and l rule: subc_term.induct subc_list.induct) simp_all

lemma subc_sub_new:
  \<open>new_term c t \<Longrightarrow> subc c (sub_term m t s) (sub m t p) = sub m t (subc c s p)\<close>
  using subc_sub_new' inc_sub' new_inc' by (induct p arbitrary: m t s) simp_all

lemma subc_sub_0_new [simp]:
  \<open>new_term c t \<Longrightarrow> subc c s (sub 0 t p) = sub 0 t (subc c (inc_term s) p)\<close>
  using subc_sub_new sub_0_inc by metis

lemma member_subc: \<open>member p z \<Longrightarrow> member (subc c s p) (subcs c s z)\<close>
  by (induct z) auto

lemma OK_subc: \<open>OK p z \<Longrightarrow> OK (subc c s p) (subcs c s z)\<close>
proof (induct p z arbitrary: c s rule: OK.induct)
  case (Assume p z)
  then show ?case
    using member_subc OK.Assume by blast
next
  case (Boole p z)
  then have \<open>OK Falsity (Neg (subc c s p) # subcs c s z)\<close>
    by simp
  then show ?case
    using OK.Boole by blast
next
  case (Imp_E p q z)
  then have
    \<open>OK (Imp (subc c s p) (subc c s q)) (subcs c s z)\<close>
    \<open>OK (subc c s p) (subcs c s z)\<close>
    by simp_all
  then show ?case
    using OK.Imp_E by blast
next
  case (Imp_I q p z)
  then show ?case
    using OK.Imp_I by simp
next
  case (Dis_E p q z r)
  then have
    \<open>OK (Dis (subc c s p) (subc c s q)) (subcs c s z)\<close>
    \<open>OK (subc c s r) (subc c s p # subcs c s z)\<close>
    \<open>OK (subc c s r) (subc c s q # subcs c s z)\<close>
    by simp_all
  then show ?case
    using OK.Dis_E by blast
next
  case (Dis_I1 p z q)
  then show ?case
    using OK.Dis_I1 by simp
next
  case (Dis_I2 q z p)
  then show ?case
    using OK.Dis_I2 by simp
next
  case (Con_E1 p q z)
  then have \<open>OK (Con (subc c s p) (subc c s q)) (subcs c s z)\<close>
    by simp
  then show ?case
    using OK.Con_E1 by blast
next
  case (Con_E2 p q z)
  then have \<open>OK (Con (subc c s p) (subc c s q)) (subcs c s z)\<close>
    by simp
  then show ?case
    using OK.Con_E2 by blast
next
  case (Con_I p z q)
  then show ?case
    using OK.Con_I by simp
next
  case (Exi_E p z q d)
  then show ?case proof (cases \<open>c = d\<close>)
    case True
    then have \<open>OK q z\<close>
      using Exi_E OK.Exi_E by blast
    moreover have \<open>new c q\<close> and \<open>news c z\<close>
      using Exi_E True by simp_all
    ultimately show ?thesis
      by simp
  next
    case False
    let ?params = \<open>params p \<union> params q \<union> (\<Union>p \<in> set z. params p) \<union> params_term s \<union> {c} \<union> {d}\<close>

    have \<open>finite ?params\<close>
      by simp
    then obtain fresh where fresh: \<open>fresh \<notin> ?params\<close>
      by (meson ex_new_if_finite infinite_UNIV_listI)

    let ?s = \<open>psubst_term (id(d := fresh)) s\<close>
    let ?f = \<open>id(d := fresh, fresh := d)\<close>

    have f: \<open>\<forall>x \<in> ?params. x \<noteq> c \<longrightarrow> ?f x \<noteq> ?f c\<close>
      using fresh by simp

    have \<open>new_term d ?s\<close>
      using fresh psubst_new_free'(1) by simp
    then have \<open>psubst_term ?f ?s = psubst_term (id(fresh := d)) ?s\<close>
      using new_params' fun_upd_twist(1) psubst_upd'(1) by metis
    then have psubst_s: \<open>psubst_term ?f ?s = s\<close>
      using fresh psubst_new_away' by simp

    have \<open>?f c = c\<close> and \<open>new_term (?f c) (Fun fresh [])\<close>
      using False fresh by auto

    have \<open>OK (subc c (psubst_term ?f ?s) (Exi p)) (subcs c (psubst_term ?f ?s) z)\<close>
      using Exi_E by blast
    then have exi_p:
      \<open>OK (Exi (subc c (inc_term (psubst_term ?f ?s)) p)) (subcs c s z)\<close>
      using psubst_s by simp

    have \<open>news d z\<close>
      using Exi_E by simp
    moreover have \<open>news fresh z\<close>
      using fresh by (induct z) simp_all
    ultimately have \<open>map (psubst ?f) z = z\<close>
      by (induct z) simp_all
    moreover have \<open>\<forall>x \<in> \<Union>p \<in> set z. params p. x \<noteq> c \<longrightarrow> ?f x \<noteq> ?f c\<close>
      by simp
    ultimately have psubst_z: \<open>map (psubst ?f) (subcs c ?s z) = subcs c s z\<close>
      using \<open>?f c = c\<close> psubst_s subcs_psubst by simp

    have \<open>psubst ?f (subc c ?s (sub 0 (Fun d []) p)) =
      subc (?f c) (psubst_term ?f ?s) (psubst ?f (sub 0 (Fun d []) p))\<close>
      using subc_psubst fresh by simp
    also have \<open>\<dots> = subc c s (sub 0 (Fun fresh []) (psubst ?f p))\<close>
      using psubst_sub psubst_s \<open>?f c = c\<close> by simp
    also have \<open>\<dots> = subc c s (sub 0 (Fun fresh []) p)\<close>
      using Exi_E fresh by simp
    finally have psubst_p: \<open>psubst ?f (subc c ?s (sub 0 (Fun d []) p)) =
        sub 0 (Fun fresh []) (subc c (inc_term s) p)\<close>
      using \<open>new_term (?f c) (Fun fresh [])\<close> \<open>?f c = c\<close> by simp

    have \<open>\<forall>x \<in> params q. x \<noteq> c \<longrightarrow> ?f x \<noteq> ?f c\<close>
      using f by blast
    then have psubst_q: \<open>psubst ?f (subc c ?s q) = subc c s q\<close>
      using Exi_E fresh \<open>?f c = c\<close> psubst_s subc_psubst f by simp

    have \<open>OK (subc c ?s q) (subcs c ?s (sub 0 (Fun d []) p # z))\<close>
      using Exi_E by blast
    then have \<open>OK (subc c ?s q) (subc c ?s (sub 0 (Fun d []) p) # subcs c ?s z)\<close>
      by simp
    then have \<open>OK (psubst ?f (subc c ?s q)) (psubst ?f (subc c ?s (sub 0 (Fun d []) p))
          # map (psubst ?f) (subcs c ?s z))\<close>
      using OK_psubst by fastforce
    then have q: \<open>OK (subc c s q) (sub 0 (Fun fresh []) (subc c (inc_term s) p) # subcs c s z)\<close>
      using psubst_q psubst_z psubst_p by simp

    have \<open>new fresh (subc c (inc_term s) p)\<close>
      using fresh new_subc new_inc' by simp
    moreover have \<open>new fresh (subc c s q)\<close>
      using fresh new_subc by simp
    moreover have \<open>news fresh (subcs c s z)\<close>
      using fresh \<open>news fresh z\<close> news_subcs by simp
    ultimately have news_pqz: \<open>news fresh (subc c (inc_term s) p # subc c s q # subcs c s z)\<close>
      by simp

    show \<open>OK (subc c s q) (subcs c s z)\<close>
      using OK.Exi_E exi_p q news_pqz psubst_s by metis
  qed
next
  case (Exi_I t p z)
  let ?params = \<open>params p \<union> (\<Union>p \<in> set z. params p) \<union> params_term s \<union> params_term t \<union> {c}\<close>

  have \<open>finite ?params\<close>
    by simp
  then obtain fresh where fresh: \<open>fresh \<notin> ?params\<close>
    by (meson ex_new_if_finite infinite_UNIV_listI)

  let ?f = \<open>id(c := fresh)\<close>
  let ?g = \<open>id(fresh := c)\<close>
  let ?s = \<open>psubst_term ?f s\<close>

  have c: \<open>?g c = c\<close>
    using fresh by simp
  have s: \<open>psubst_term ?g ?s = s\<close>
    using fresh psubst_new_away' by simp
  have p: \<open>psubst ?g (Exi p) = Exi p\<close>
    using fresh psubst_new_away by simp

  have \<open>\<forall>x \<in> (\<Union>p \<in> set z. params p). x \<noteq> c \<longrightarrow> ?g x \<noteq> ?g c\<close>
    using fresh by auto
  moreover have \<open>map (psubst ?g) z = z\<close>
    using fresh by (induct z) simp_all
  ultimately have z: \<open>map (psubst ?g) (subcs c ?s z) = subcs c s z\<close>
    using s subcs_psubst by simp

  have \<open>new_term c ?s\<close>
    using fresh psubst_new_free' by simp
  then have \<open>OK (subc c ?s (sub 0 (subc_term c ?s t) p)) (subcs c ?s z)\<close>
    using Exi_I new_subc_put by metis
  moreover have \<open>new_term c (subc_term c ?s t)\<close>
    using \<open>new_term c ?s\<close> new_subc_same' by blast
  ultimately have \<open>OK (sub 0 (subc_term c ?s t) (subc c (inc_term ?s) p)) (subcs c ?s z)\<close>
    by simp

  then have \<open>OK (subc c ?s (Exi p)) (subcs c ?s z)\<close>
    using OK.Exi_I by simp
  then have \<open>OK (psubst ?g (subc c ?s (Exi p))) (map (psubst ?g) (subcs c ?s z))\<close>
    using OK_psubst by blast
  moreover have \<open>\<forall>x \<in> params (Exi p). x \<noteq> c \<longrightarrow> ?g x \<noteq> ?g c\<close>
    using fresh by auto
  ultimately show \<open>OK (subc c s (Exi p)) (subcs c s z)\<close>
    using subc_psubst c s p z by simp
next
  case (Uni_E p z t)
  let ?params = \<open>params p \<union> (\<Union>p \<in> set z. params p) \<union> params_term s \<union> params_term t \<union> {c}\<close>

  have \<open>finite ?params\<close>
    by simp
  then obtain fresh where fresh: \<open>fresh \<notin> ?params\<close>
    by (meson ex_new_if_finite infinite_UNIV_listI)

  let ?f = \<open>id(c := fresh)\<close>
  let ?g = \<open>id(fresh := c)\<close>
  let ?s = \<open>psubst_term ?f s\<close>

  have c: \<open>?g c = c\<close>
    using fresh by simp
  have s: \<open>psubst_term ?g ?s = s\<close>
    using fresh psubst_new_away' by simp
  have p: \<open>psubst ?g (sub 0 t p) = sub 0 t p\<close>
    using fresh psubst_new psubst_sub sub_new psubst_new'(1) by auto

  have \<open>\<forall>x \<in> (\<Union>p \<in> set z. params p). x \<noteq> c \<longrightarrow> ?g x \<noteq> ?g c\<close>
    using fresh by auto
  moreover have \<open>map (psubst ?g) z = z\<close>
    using fresh by (induct z) simp_all
  ultimately have z: \<open>map (psubst ?g) (subcs c ?s z) = subcs c s z\<close>
    using s subcs_psubst by simp

  have \<open>new_term c ?s\<close>
    using fresh psubst_new_free' by simp

  have \<open>OK (Uni (subc c (inc_term ?s) p)) (subcs c ?s z)\<close>
    using Uni_E by simp
  then have \<open>OK (sub 0 (subc_term c ?s t) (subc c (inc_term ?s) p)) (subcs c ?s z)\<close>
    using OK.Uni_E by blast
  moreover have \<open>new_term c (subc_term c ?s t)\<close>
    using \<open>new_term c ?s\<close> new_subc_same' by blast
  ultimately have \<open>OK (subc c ?s (sub 0 (subc_term c ?s t) p)) (subcs c ?s z)\<close>
    by simp
  then have \<open>OK (subc c ?s (sub 0 t p)) (subcs c ?s z)\<close>
    using new_subc_put \<open>new_term c ?s\<close> by metis
  then have \<open>OK (psubst ?g (subc c ?s (sub 0 t p))) (map (psubst ?g) (subcs c ?s z))\<close>
    using OK_psubst by blast
  moreover have \<open>\<forall>x \<in> params (sub 0 t p). x \<noteq> c \<longrightarrow> ?g x \<noteq> ?g c\<close>
    using fresh p psubst_new_free new_params by (metis fun_upd_apply id_apply)
  ultimately show \<open>OK (subc c s (sub 0 t p)) (subcs c s z)\<close>
    using subc_psubst c s p z by simp
next
  case (Uni_I d p z)
  then show ?case proof (cases \<open>c = d\<close>)
    case True
    then have \<open>OK (Uni p) z\<close>
      using Uni_I OK.Uni_I by blast
    moreover have \<open>new c p\<close> and \<open>news c z\<close>
      using Uni_I True by simp_all
    ultimately show ?thesis
      by simp
  next
    case False
    let ?params = \<open>params p \<union> (\<Union>p \<in> set z. params p) \<union> params_term s \<union> {c} \<union> {d}\<close>

    have \<open>finite ?params\<close>
      by simp
    then obtain fresh where fresh: \<open>fresh \<notin> ?params\<close>
      by (meson ex_new_if_finite infinite_UNIV_listI)

    let ?s = \<open>psubst_term (id(d := fresh)) s\<close>
    let ?f = \<open>id(d := fresh, fresh := d)\<close>

    have f: \<open>\<forall>x \<in> ?params. x \<noteq> c \<longrightarrow> ?f x \<noteq> ?f c\<close>
      using fresh by simp

    have \<open>new_term d ?s\<close>
      using fresh psubst_new_free' by simp
    then have \<open>psubst_term ?f ?s = psubst_term (id(fresh := d)) ?s\<close>
      using new_params' fun_upd_twist(1) psubst_upd'(1) by metis
    then have psubst_s: \<open>psubst_term ?f ?s = s\<close>
      using fresh psubst_new_away' by simp

    have \<open>?f c = c\<close> and \<open>new_term c (Fun fresh [])\<close>
      using False fresh by auto

    have \<open>psubst ?f (subc c ?s (sub 0 (Fun d []) p)) =
      subc (?f c) (psubst_term ?f ?s) (psubst ?f (sub 0 (Fun d []) p))\<close>
      using subc_psubst by simp
    also have \<open>\<dots> = subc c s (sub 0 (Fun fresh []) (psubst ?f p))\<close>
      using \<open>?f c = c\<close> psubst_sub psubst_s by simp
    also have \<open>\<dots> = subc c s (sub 0 (Fun fresh []) p)\<close>
      using Uni_I fresh by simp
    finally have psubst_p: \<open>psubst ?f (subc c ?s (sub 0 (Fun d []) p)) =
        sub 0 (Fun fresh []) (subc c (inc_term s) p)\<close>
      using \<open>new_term c (Fun fresh [])\<close> by simp

    have \<open>news d z\<close>
      using Uni_I by simp
    moreover have \<open>news fresh z\<close>
      using fresh by (induct z) simp_all
    ultimately have \<open>map (psubst ?f) z = z\<close>
      by (induct z) simp_all
    moreover have \<open>\<forall>x \<in> \<Union>p \<in> set z. params p. x \<noteq> c \<longrightarrow> ?f x \<noteq> ?f c\<close>
      by auto
    ultimately have psubst_z: \<open>map (psubst ?f) (subcs c ?s z) = subcs c s z\<close>
      using \<open>?f c = c\<close> psubst_s subcs_psubst by simp

    have \<open>OK (subc c ?s (sub 0 (Fun d []) p)) (subcs c ?s z)\<close>
      using Uni_I by blast
    then have \<open>OK (psubst ?f (subc c ?s (sub 0 (Fun d []) p))) (map (psubst ?f) (subcs c ?s z))\<close>
      using OK_psubst by fastforce
    then have \<open>OK (psubst ?f (subc c ?s (sub 0 (Fun d []) p))) (subcs c s z)\<close>
      using psubst_z by simp
    then have sub_p: \<open>OK (sub 0 (Fun fresh []) (subc c (inc_term s) p)) (subcs c s z)\<close>
      using psubst_p by simp

    have \<open>new_term fresh s\<close>
      using fresh by simp
    then have \<open>new_term fresh (inc_term s)\<close>
      using new_inc' by simp
    then have \<open>new fresh (subc c (inc_term s) p)\<close>
      using fresh new_subc by simp
    moreover have \<open>news fresh (subcs c s z)\<close>
      using \<open>news fresh z\<close> \<open>new_term fresh s\<close> news_subcs by fast
    ultimately show \<open>OK (subc c s (Uni p)) (subcs c s z)\<close>
      using OK.Uni_I sub_p by simp
  qed
qed

subsection \<open>Weakening assumptions\<close>

lemma psubst_new_subset:
  assumes \<open>set z \<subseteq> set z'\<close> \<open>c \<notin> (\<Union>p \<in> set z. params p)\<close>
  shows \<open>set z \<subseteq> set (map (psubst (id(c := n))) z')\<close>
  using assms by force

lemma subset_cons: \<open>set z \<subseteq> set z' \<Longrightarrow> set (p # z) \<subseteq> set (p # z')\<close>
  by auto

lemma weaken_assumptions: \<open>OK p z \<Longrightarrow> set z \<subseteq> set z' \<Longrightarrow> OK p z'\<close>
proof (induct p z arbitrary: z' rule: OK.induct)
  case (Assume p z)
  then show ?case
    using OK.Assume by auto
next
  case (Boole p z)
  then have \<open>OK Falsity (Neg p # z')\<close>
    using subset_cons by metis
  then show ?case
    using OK.Boole by blast
next
  case (Imp_E p q z)
  then show ?case
    using OK.Imp_E by blast
next
  case (Imp_I q p z)
  then have \<open>OK q (p # z')\<close>
    using subset_cons by metis
  then show ?case
    using OK.Imp_I by blast
next
  case (Dis_E p q z r)
  then have \<open>OK r (p # z')\<close> \<open>OK r (q # z')\<close>
    using subset_cons by metis+
  then show ?case
    using OK.Dis_E Dis_E by blast
next
  case (Dis_I1 p z q)
  then show ?case
    using OK.Dis_I1 by blast
next
  case (Dis_I2 q z p)
  then show ?case
    using OK.Dis_I2 by blast
next
  case (Con_E1 p q z)
  then show ?case
    using OK.Con_E1 by blast
next
  case (Con_E2 p q z)
  then show ?case
    using OK.Con_E2 by blast
next
  case (Con_I p z q)
  then show ?case
    using OK.Con_I by blast
next
  case (Exi_E p z q c)
  let ?params = \<open>params p \<union> params q \<union> (\<Union>p \<in> set z'. params p) \<union> {c}\<close>

  have \<open>finite ?params\<close>
    by simp
  then obtain fresh where \<open>fresh \<notin> ?params\<close>
    by (meson ex_new_if_finite List.finite_set infinite_UNIV_listI)
  then have fresh: \<open>new fresh p \<and> new fresh q \<and> news fresh z' \<and> fresh \<noteq> c\<close>
    using allnew new_params by (metis Ball_set UN_iff UnI1 UnI2 insertCI)

  let ?z' = \<open>map (psubst (id(c := fresh))) z'\<close>

  have \<open>news c z\<close>
    using Exi_E by simp
  then have \<open>set z \<subseteq> set ?z'\<close>
    using Exi_E psubst_new_subset by (simp add: Ball_set)
  then have \<open>OK (Exi p) ?z'\<close>
    using Exi_E by blast

  moreover have \<open>set (sub 0 (Fun c []) p # z) \<subseteq> set (sub 0 (Fun c []) p # ?z')\<close>
    using \<open>set z \<subseteq> set ?z'\<close> by auto
  then have \<open>OK q (sub 0 (Fun c []) p # ?z')\<close>
    using Exi_E by blast

  moreover have \<open>news c ?z'\<close>
    using fresh map_psubst_new_free by simp
  then have \<open>news c (p # q # ?z')\<close>
    using Exi_E by simp

  ultimately have \<open>OK q ?z'\<close>
    using Exi_E OK.Exi_E by blast

  then have \<open>OK (psubst (id(fresh := c)) q) (map (psubst (id(fresh := c))) ?z')\<close>
    using OK_psubst by blast
  moreover have \<open>map (psubst (id(fresh := c))) ?z' = z'\<close>
    using fresh map_psubst_new_away by blast
  moreover have \<open>psubst (id(fresh := c)) q = q\<close>
    using fresh by simp
  ultimately show \<open>OK q z'\<close>
    by simp
next
  case (Exi_I t p z)
  then show ?case
    using OK.Exi_I by blast
next
  case (Uni_E p z t)
  then show ?case
    using OK.Uni_E by blast
next
  case (Uni_I c p z)
  let ?params = \<open>params p \<union> (\<Union>p \<in> set z'. params p) \<union> {c}\<close>

  have \<open>finite ?params\<close>
    by simp
  then obtain fresh where \<open>fresh \<notin> ?params\<close>
    by (meson ex_new_if_finite List.finite_set infinite_UNIV_listI)
  then have fresh: \<open>new fresh p \<and> news fresh z' \<and> fresh \<noteq> c\<close>
    using allnew new_params by (metis Ball_set UN_iff UnI1 UnI2 insertCI)

  let ?z' = \<open>map (psubst (id(c := fresh))) z'\<close>

  have \<open>news c z\<close>
    using Uni_I by simp
  then have \<open>set z \<subseteq> set ?z'\<close>
    using Uni_I psubst_new_subset allnew new_params map_psubst_new image_set subset_image_iff
    by (metis (no_types))
  then have \<open>OK (sub 0 (Fun c []) p) ?z'\<close>
    using Uni_I by blast

  moreover have \<open>\<forall>p \<in> set ?z'. c \<notin> params p\<close>
    using fresh psubst_new_free by simp
  then have \<open>list_all (\<lambda>p. c \<notin> params p) (p # ?z')\<close>
    using Uni_I by (simp add: list_all_iff)
  then have \<open>news c (p # ?z')\<close>
    by simp

  ultimately have \<open>OK (Uni p) ?z'\<close>
    using Uni_I OK.Uni_I by blast

  then have \<open>OK (psubst (id(fresh := c)) (Uni p)) (map (psubst (id(fresh := c))) ?z')\<close>
    using OK_psubst by blast
  moreover have \<open>map (psubst (id(fresh := c))) ?z' = z'\<close>
    using fresh map_psubst_new_away by blast
  moreover have \<open>psubst (id(fresh := c)) (Uni p) = Uni p\<close>
    using fresh Uni_I by simp
  ultimately show \<open>OK (Uni p) z'\<close>
    by simp
qed

subsection \<open>Implications and assumptions\<close>

primrec put_imps :: \<open>fm \<Rightarrow> fm list \<Rightarrow> fm\<close> where
  \<open>put_imps p [] = p\<close> |
  \<open>put_imps p (q # z) = Imp q (put_imps p z)\<close>

lemma semantics_put_imps:
  \<open>(list_all (semantics e f g) z \<longrightarrow> semantics e f g p) = semantics e f g (put_imps p z)\<close>
  by (induct z) auto

lemma shift_imp_assum:
  assumes \<open>OK (Imp p q) z\<close>
  shows \<open>OK q (p # z)\<close>
proof -
  have \<open>set z \<subseteq> set (p # z)\<close>
    by auto
  then have \<open>OK (Imp p q) (p # z)\<close>
    using assms weaken_assumptions by blast
  moreover have \<open>OK p (p # z)\<close>
    using Assume by simp
  ultimately show \<open>OK q (p # z)\<close>
    using Imp_E by blast
qed

lemma remove_imps: \<open>OK (put_imps p z) z' \<Longrightarrow> OK p (rev z @ z')\<close>
  using shift_imp_assum by (induct z arbitrary: z') simp_all

subsection \<open>Closure elimination\<close>

lemma subc_sub_closed_var' [simp]:
  \<open>new_term c t \<Longrightarrow> closed_term (Suc m) t \<Longrightarrow> subc_term c (Var m) (sub_term m (Fun c []) t) = t\<close>
  \<open>new_list c l \<Longrightarrow> closed_list (Suc m) l \<Longrightarrow> subc_list c (Var m) (sub_list m (Fun c []) l) = l\<close>
  by (induct t and l rule: sub_term.induct sub_list.induct) auto

lemma subc_sub_closed_var [simp]: \<open>new c p \<Longrightarrow> closed (Suc m) p \<Longrightarrow>
    subc c (Var m) (sub m (Fun c []) p) = p\<close>
  by (induct p arbitrary: m) simp_all

primrec put_unis :: \<open>nat \<Rightarrow> fm \<Rightarrow> fm\<close> where
  \<open>put_unis 0 p = p\<close> |
  \<open>put_unis (Suc m) p = Uni (put_unis m p)\<close>

lemma sub_put_unis [simp]: \<open>sub i (Fun c []) (put_unis k p) = put_unis k (sub (i + k) (Fun c []) p)\<close>
  by (induct k arbitrary: i) simp_all

lemma closed_put_unis [simp]: \<open>closed m (put_unis k p) = closed (m + k) p\<close>
  by (induct k arbitrary: m) simp_all

lemma valid_put_unis: \<open>\<forall>(e :: nat \<Rightarrow> 'a) f g. semantics e f g p \<Longrightarrow>
    semantics (e :: nat \<Rightarrow> 'a) f g (put_unis m p)\<close>
  by (induct m arbitrary: e) simp_all

lemma put_unis_collapse: \<open>put_unis m (put_unis n p) = put_unis (m + n) p\<close>
  by (induct m) simp_all

fun consts_for_unis :: \<open>fm \<Rightarrow> id list \<Rightarrow> fm\<close> where
  \<open>consts_for_unis (Uni p) (c#cs) = consts_for_unis (sub 0 (Fun c []) p) cs\<close> |
  \<open>consts_for_unis p _ = p\<close>

lemma consts_for_unis: \<open>OK (put_unis (length cs) p) [] \<Longrightarrow>
  OK (consts_for_unis (put_unis (length cs) p) cs) []\<close>
proof (induct cs arbitrary: p)
  case (Cons c cs)
  then have \<open>OK (Uni (put_unis (length cs) p)) []\<close>
    by simp
  then have \<open>OK (sub 0 (Fun c []) (put_unis (length cs) p)) []\<close>
    using Uni_E by blast
  then show ?case
    using Cons by simp
qed simp

primrec vars_for_consts :: \<open>fm \<Rightarrow> id list \<Rightarrow> fm\<close> where
  \<open>vars_for_consts p [] = p\<close> |
  \<open>vars_for_consts p (c # cs) = subc c (Var (length cs)) (vars_for_consts p cs)\<close>

lemma vars_for_consts: \<open>OK p [] \<Longrightarrow> OK (vars_for_consts p xs) []\<close>
  using OK_subc by (induct xs arbitrary: p) fastforce+

lemma vars_for_consts_for_unis:
  \<open>closed (length cs) p \<Longrightarrow> list_all (\<lambda>c. new c p) cs \<Longrightarrow> distinct cs \<Longrightarrow>
   vars_for_consts (consts_for_unis (put_unis (length cs) p) cs) cs = p\<close>
  using sub_new_all by (induct cs arbitrary: p) (auto simp: list_all_iff)

lemma fresh_constant: \<open>\<exists>c. c \<notin> set cs \<and> new c p\<close>
proof -
  have \<open>finite (set cs \<union> params p)\<close>
    by simp
  then show ?thesis
    using ex_new_if_finite UnI1 UnI2 infinite_UNIV_listI new_params by metis
qed

lemma fresh_constants:
  assumes \<open>sentence (put_unis m p)\<close>
  shows \<open>\<exists>cs. length cs = m \<and> list_all (\<lambda>c. new c p) cs \<and> distinct cs\<close>
proof (induct m)
  case (Suc m)
  then obtain cs where \<open>length cs = m \<and> list_all (\<lambda>c. new c p) cs \<and> distinct cs\<close>
    by blast
  moreover obtain c where \<open>c \<notin> set cs \<and> new c p\<close>
    using Suc fresh_constant by blast
  ultimately have \<open>length (c # cs) = Suc m \<and> list_all (\<lambda>c. new c p) (c # cs) \<and> distinct (c # cs)\<close>
    by simp
  then show ?case
    by blast
qed simp

lemma closed_max:
  assumes \<open>closed m p\<close> \<open>closed n q\<close>
  shows \<open>closed (max m n) p \<and> closed (max m n) q\<close>
proof -
  have \<open>m \<le> max m n\<close> and \<open>n \<le> max m n\<close>
    by simp_all
  then show ?thesis
    using assms closed_mono by metis
qed

lemma ex_closed' [simp]: \<open>\<exists>m. closed_term m t\<close> \<open>\<exists>n. closed_list n l\<close>
proof (induct t and l rule: closed_term.induct closed_list.induct)
  case (Cons_tm t l)
  then obtain m and n where \<open>closed_term m t\<close> and \<open>closed_list n l\<close>
    by blast
  moreover have \<open>m \<le> max m n\<close> and \<open>n \<le> max m n\<close>
    by simp_all
  ultimately have \<open>closed_term (max m n) t\<close> and \<open>closed_list (max m n) l\<close>
    using closed_mono' by blast+
  then show ?case
    by auto
qed auto

lemma ex_closed [simp]: \<open>\<exists>m. closed m p\<close>
proof (induct p)
  case (Imp p q)
  then show ?case
    using closed_max by fastforce
next
  case (Dis p q)
  then show ?case
    using closed_max by fastforce
next
  case (Con p q)
  then show ?case
    using closed_max by fastforce
next
  case (Exi p)
  then obtain m where \<open>closed m p\<close>
    by blast
  then have \<open>closed (Suc m) p\<close>
    using closed_mono Suc_n_not_le_n nat_le_linear by blast
  then show ?case
    by auto
next
  case (Uni p)
  then obtain m where \<open>closed m p\<close>
    by blast
  then have \<open>closed (Suc m) p\<close>
    using closed_mono Suc_n_not_le_n nat_le_linear by blast
  then show ?case
    by auto
qed simp_all

lemma ex_closure: \<open>\<exists>m. sentence (put_unis m p)\<close>
  by simp

lemma remove_unis_sentence:
  assumes \<open>sentence (put_unis m p)\<close> \<open>OK (put_unis m p) []\<close>
  shows \<open>OK p []\<close>
proof -
  obtain cs :: \<open>id list\<close> where \<open>length cs = m\<close>
    and *: \<open>distinct cs\<close> and **: \<open>list_all (\<lambda>c. new c p) cs\<close>
    using assms fresh_constants by blast
  then have \<open>OK (consts_for_unis (put_unis (length cs) p) cs) []\<close>
    using assms consts_for_unis by blast
  then have \<open>OK (vars_for_consts (consts_for_unis (put_unis (length cs) p) cs) cs) []\<close>
    using vars_for_consts by blast
  moreover have \<open>closed (length cs) p\<close>
    using assms \<open>length cs = m\<close> by simp
  ultimately show \<open>OK p []\<close>
    using vars_for_consts_for_unis * ** by simp
qed

subsection \<open>Completeness\<close>

theorem completeness':
  assumes \<open>\<forall>(e :: nat \<Rightarrow> 'a) f g. list_all (semantics e f g) z \<longrightarrow> semantics e f g p\<close>
    and \<open>denumerable (UNIV :: 'a set)\<close>
  shows \<open>OK p z\<close>
proof -
  let ?p = \<open>put_imps p (rev z)\<close>

  have *: \<open>\<forall>(e :: nat \<Rightarrow> 'a) f g. semantics e f g ?p\<close>
    using assms(1) semantics_put_imps by fastforce
  obtain m where **: \<open>sentence (put_unis m ?p)\<close>
    using ex_closure by blast
  moreover have \<open>\<forall>(e :: nat \<Rightarrow> 'a) f g. semantics e f g (put_unis m ?p)\<close>
    using * valid_put_unis by blast
  ultimately have \<open>OK (put_unis m ?p) []\<close>
    using assms(2) sentence_completeness by blast
  then have \<open>OK ?p []\<close>
    using ** remove_unis_sentence by blast
  then show \<open>OK p z\<close>
    using remove_imps by fastforce
qed

theorem completeness:
  assumes \<open>\<forall>(e :: nat \<Rightarrow> 'a) f g. semantics e f g p\<close>
    and \<open>denumerable (UNIV :: 'a set)\<close>
  shows \<open>OK p []\<close>
  using assms by (simp add: completeness')

corollary \<open>\<forall>(e :: nat \<Rightarrow> nat) f g. semantics e f g p \<Longrightarrow> OK p []\<close>
  using completeness denumerable_bij by blast

section \<open>Main Result\<close> \<comment> \<open>NaDeA is sound and complete\<close>

abbreviation \<open>valid p \<equiv> \<forall>(e :: nat \<Rightarrow> nat) f g. semantics e f g p\<close>

theorem main: \<open>valid p \<longleftrightarrow> OK p []\<close>
proof
  assume \<open>valid p\<close>
  with completeness show \<open>OK p []\<close>
    using denumerable_bij by blast
next
  assume \<open>OK p []\<close>
  with soundness show \<open>valid p\<close>
    by (intro allI)
qed

corollary \<open>valid p \<longrightarrow> semantics e f g p\<close>
proof
  assume \<open>valid p\<close>
  then have \<open>OK p []\<close>
    unfolding main .
  with soundness show \<open>semantics e f g p\<close> .
qed

theorem any_unis: \<open>OK (put_unis k p) [] \<Longrightarrow> OK (put_unis m p) []\<close>
  using main ex_closure put_unis_collapse remove_unis_sentence valid_put_unis by metis

corollary \<open>OK p [] \<Longrightarrow> OK (put_unis m p) []\<close> \<open>OK (put_unis m p) [] \<Longrightarrow> OK p []\<close>
  using any_unis put_unis.simps(1) by metis+

section \<open>Acknowledgements\<close>

text \<open>
Based on:

  \<^item> Stefan Berghofer:
  First-Order Logic According to Fitting.
  \<^url>\<open>https://www.isa-afp.org/entries/FOL-Fitting.shtml\<close>

  \<^item> Anders Schlichtkrull:
  The Resolution Calculus for First-Order Logic.
  \<^url>\<open>https://www.isa-afp.org/entries/Resolution_FOL.shtml\<close>

  \<^item> Jørgen Villadsen, Andreas Halkjær From, Alexander Birch Jensen & Anders Schlichtkrull:
  NaDeA - Natural Deduction Assistant.
  \<^url>\<open>https://github.com/logic-tools/nadea\<close>
\<close>

end
