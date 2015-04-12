text \<open>\section*{Soundness Proof}\<close>

theory NaDeA imports Main begin

type_synonym id = string

datatype tm = Var nat | Fun id "tm list"

datatype fm = Falsity | Pre id "tm list" | Imp fm fm | Dis fm fm | Con fm fm | Exi fm | Uni fm

primrec
  semantics_term :: "(nat => 'u) => (id => 'u list => 'u) => tm => 'u"
and
  semantics_list :: "(nat => 'u) => (id => 'u list => 'u) => tm list => 'u list"
where
"semantics_term e f (Var v) = e v" |
"semantics_term e f (Fun i l) = f i (semantics_list e f l)" |
"semantics_list e f [] = []" |
"semantics_list e f (t # l) = semantics_term e f t # semantics_list e f l"

primrec
  semantics :: "(nat => 'u) => (id => 'u list => 'u) => (id => 'u list => bool) => fm => bool"
where
"semantics e f g Falsity = False" |
"semantics e f g (Pre i l) = g i (semantics_list e f l)" |
"semantics e f g (Imp p q) = (if semantics e f g p then semantics e f g q else True)" |
"semantics e f g (Dis p q) = (if semantics e f g p then True else semantics e f g q)" |
"semantics e f g (Con p q) = (if semantics e f g p then semantics e f g q else False)" |
"semantics e f g (Exi p) = (? x. semantics (% n. if n = 0 then x else e (n - 1)) f g p)" |
"semantics e f g (Uni p) = (! x. semantics (% n. if n = 0 then x else e (n - 1)) f g p)"

primrec
  member :: "fm => fm list => bool"
where
"member p [] = False" |
"member p (q # a) = (if p = q then True else member p a)"

primrec
  new_term :: "id => tm => bool"
and
  new_list :: "id => tm list => bool"
where
"new_term c (Var v) = True" |
"new_term c (Fun i l) = (if i = c then False else new_list c l)" |
"new_list c [] = True" |
"new_list c (t # l) = (if new_term c t then new_list c l else False)"

primrec
  new :: "id => fm => bool"
where
"new c Falsity = True" |
"new c (Pre i l) = new_list c l" |
"new c (Imp p q) = (if new c p then new c q else False)" |
"new c (Dis p q) = (if new c p then new c q else False)" |
"new c (Con p q) = (if new c p then new c q else False)" |
"new c (Exi p) = new c p" |
"new c (Uni p) = new c p"

primrec
  news :: "id => fm list => bool"
where
"news c [] = True" |
"news c (p # a) = (if new c p then news c a else False)"

primrec
  inc_term :: "tm => tm"
and
  inc_list :: "tm list => tm list"
where
"inc_term (Var v) = Var (v + 1)" |
"inc_term (Fun i l) = Fun i (inc_list l)" |
"inc_list [] = []" |
"inc_list (t # l) = inc_term t # inc_list l"

primrec
  sub_term :: "nat => tm => tm => tm"
and
  sub_list :: "nat => tm => tm list => tm list"
where
"sub_term n s (Var v) = (if v = n then s else if v > n then Var (v - 1) else Var v)" |
"sub_term n s (Fun i l) = Fun i (sub_list n s l)" |
"sub_list n s [] = []" |
"sub_list n s (t # l) = sub_term n s t # sub_list n s l"

primrec
  sub :: "nat => tm => fm => fm"
where
"sub n s Falsity = Falsity" |
"sub n s (Pre i l) = Pre i (sub_list n s l)" |
"sub n s (Imp p q) = Imp (sub n s p) (sub n s q)" |
"sub n s (Dis p q) = Dis (sub n s p) (sub n s q)" |
"sub n s (Con p q) = Con (sub n s p) (sub n s q)" |
"sub n s (Exi p) = Exi (sub (n + 1) (inc_term s) p)" |
"sub n s (Uni p) = Uni (sub (n + 1) (inc_term s) p)"

inductive
  OK :: "fm => fm list => bool"
where
Assume:
        "member p a ==> OK p a" |
Boole:
        "OK Falsity ((Imp p Falsity) # a) ==> OK p a" |
Imp_E:
        "OK (Imp p q) a ==> OK p a ==> OK q a" |
Imp_I:
        "OK q (p # a) ==> OK (Imp p q) a" |
Dis_E:
        "OK (Dis p q) a ==> OK r (p # a) ==> OK r (q # a) ==> OK r a" |
Dis_I1:
        "OK p a ==> OK (Dis p q) a" |
Dis_I2:
        "OK q a ==> OK (Dis p q) a" |
Con_E1:
        "OK (Con p q) a ==> OK p a" |
Con_E2:
        "OK (Con p q) a ==> OK q a" |
Con_I:
        "OK p a ==> OK q a ==> OK (Con p q) a" |
Exi_E:
        "OK (Exi p) a ==> OK q ((sub 0 (Fun c []) p) # a) ==> news c (p # q # a) ==> OK q a" |
Exi_I:
        "OK (sub 0 t p) a ==> OK (Exi p) a" |
Uni_E:
        "OK (Uni p) a ==> OK (sub 0 t p) a" |
Uni_I:
        "OK (sub 0 (Fun c []) p) a ==> news c (p # a) ==> OK (Uni p) a"

(* Proof inspired by First-Order Logic According to Fitting by Stefan Berghofer *)

definition
  shift :: "(nat \<Rightarrow> 'u) \<Rightarrow> nat \<Rightarrow> 'u \<Rightarrow> nat \<Rightarrow> 'u" ("_\<langle>_:_\<rangle>" [90, 0, 0] 91)
where
"e\<langle>i:a\<rangle> = (\<lambda>j. if j < i then e j else if j = i then a else e (j - 1))"

lemma generalize_upd: "(%n. if n = 0 then z else e (n - 1)) = e\<langle>0:z\<rangle>"
unfolding shift_def by auto

lemma newness: "news c (p # a) \<Longrightarrow> new c p" "news c (p # a) \<Longrightarrow> news c a"
using news.simps by metis+

lemma membership[simp]: "member x xs \<Longrightarrow> x \<in> set xs"
by (induct xs) (auto, metis)

lemma upd_lemma':
  "new_term n t \<Longrightarrow> semantics_term e (f(n := x)) t = semantics_term e f t"
  "new_list n ts \<Longrightarrow> semantics_list e (f(n := x)) ts = semantics_list e f ts"
by (induct t and ts rule: semantics_term.induct semantics_list.induct, auto, metis+)

lemma upd_lemma: "new n p \<Longrightarrow> semantics e (f(n := x)) g p = semantics e f g p"
by (induct p arbitrary: e, simp_all add: upd_lemma', metis+)

lemma list_upd_lemma: "news n a \<Longrightarrow>
  list_all (semantics e (f(n := x)) g) a = list_all (semantics e f g) a"
by (induct a, auto, metis upd_lemma, metis, metis upd_lemma, metis)

lemma shift_eq: "i = j \<Longrightarrow> (e\<langle>i:T\<rangle>) j = T"
by (simp add: shift_def)

lemma shift_gt: "j < i \<Longrightarrow> (e\<langle>i:T\<rangle>) j = e j"
by (simp add: shift_def)

lemma shift_lt: "i < j \<Longrightarrow> (e\<langle>i:T\<rangle>) j = e (j - 1)"
by (simp add: shift_def)

lemma shift_commute: "e\<langle>i:U\<rangle>\<langle>0:T\<rangle> = e\<langle>0:T\<rangle>\<langle>Suc i:U\<rangle>"
by (rule ext, case_tac x, simp add: shift_eq shift_gt, case_tac nat, simp_all add: shift_def)

lemma lift_lemma:
  "semantics_term (e\<langle>0:z\<rangle>) f (inc_term t) = semantics_term e f t"
  "semantics_list (e\<langle>0:z\<rangle>) f (inc_list ts) = semantics_list e f ts"
by (induct t and ts rule: semantics_term.induct semantics_list.induct) (simp_all add: shift_lt)

lemma subst_lemma':
  "semantics_term e f (sub_term i u t) = semantics_term (e\<langle>i:semantics_term e f u\<rangle>) f t"
  "semantics_list e f (sub_list i u ts) = semantics_list (e\<langle>i:semantics_term e f u\<rangle>) f ts"
by (induct t and ts rule: semantics_term.induct semantics_list.induct)
  (simp_all add: shift_eq shift_gt shift_lt)

lemma Exi_simp2: "semantics e f g (Exi p) = (? x. semantics (e\<langle>0:x\<rangle>) f g p)"
unfolding shift_def by auto

lemma Uni_simp2: "semantics e f g (Uni p) = (! x. semantics (e\<langle>0:x\<rangle>) f g p)"
unfolding shift_def by auto

lemma subst_lemma: "semantics e f g (sub i t a) = semantics (e\<langle>i:semantics_term e f t\<rangle>) f g a"
proof (induct a arbitrary: e t i)
  case (Pre p ts)
  show ?case using subst_lemma'[of e] by auto
next
  case (Uni a)
  have "semantics (e\<langle>i:semantics_term e f t\<rangle>) f g (Uni a)
            = (\<forall>z. semantics (e\<langle>i:semantics_term e f t\<rangle>\<langle>0:z\<rangle>) f g a)"
    using Uni_simp2 by simp
  also
  have "... = (\<forall>z. semantics (e\<langle>0:z\<rangle>\<langle>i + 1:semantics_term e f t\<rangle>) f g a)"
    using shift_commute[of e] by auto
  also
  have "... = (\<forall>z. semantics (e\<langle>0:z\<rangle>\<langle>i + 1:semantics_term (e\<langle>0:z\<rangle>) f (inc_term t)\<rangle>) f g a)"
    using lift_lemma[of e] by simp
  also
  have "... = (\<forall>z. semantics (e\<langle>0:z\<rangle>) f g (sub (i + 1) (inc_term t) a))" using Uni by simp
  also
  have "... = semantics e f g (Uni (sub (i + 1) (inc_term t) a))" using Uni_simp2[of e] by simp
  also
  have "... = semantics e f g (sub i t (Uni a)) " by auto
  finally show ?case by simp
next
  case (Exi a)
  have "semantics (e\<langle>i:semantics_term e f t\<rangle>) f g (Exi a)
            = (\<exists>z. semantics (e\<langle>i:semantics_term e f t\<rangle>\<langle>0:z\<rangle>) f g a)" using Exi_simp2 by simp
  also
  have "... = (\<exists>z. semantics (e\<langle>0:z\<rangle>\<langle>i + 1:semantics_term e f t\<rangle>) f g a)"
    using shift_commute[of e] by auto
  also
  have "... = (\<exists>z. semantics (e\<langle>0:z\<rangle>\<langle>i + 1:semantics_term (e\<langle>0:z\<rangle>) f (inc_term t)\<rangle>) f g a)"
    using lift_lemma[of e] by simp
  also
  have "... = (\<exists>z. semantics (e\<langle>0:z\<rangle>) f g (sub (i + 1) (inc_term t) a))" using Exi by simp
  also
  have "... = semantics e f g (Exi (sub (i + 1) (inc_term t) a))" using Exi_simp2[of e] by simp
  also
  have "... = semantics e f g (sub i t (Exi a)) " by auto
  finally show ?case by simp
qed auto

lemma subst_lemma2:
  "semantics e f g (sub 0 t a) =
          semantics (%n. if n = 0 then semantics_term e f t else e(n - 1)) f g a"
using subst_lemma[of e] unfolding shift_def by auto

lemma soundness': "OK p a \<Longrightarrow> list_all (semantics e f g) a \<Longrightarrow> semantics e f g p"
proof (induct arbitrary: e f rule: OK.induct)
  case (Assume p a)
  then have "p \<in> set a" by auto
  moreover
  from Assume have "\<forall>p \<in> set a. semantics e f g p" by (metis list_all_iff)
  ultimately show ?case by auto
next
  case (Boole p a)
  then have "list_all (semantics e f g) (Imp p Falsity # a) \<Longrightarrow> False" by auto
  then have "\<not>list_all (semantics e f g) (Imp p Falsity # a)" by auto
  then have "\<not>semantics e f g (Imp p Falsity)" using Boole by (metis list.pred_inject(2))
  then have "semantics e f g p \<and> \<not>semantics e f g Falsity" using semantics.simps(3) by metis
  then show ?case by auto
next
  case (Dis_E p q a r)
  then have "semantics e f g (Dis p q)" by auto
  then have "semantics e f g p \<or> semantics e f g q" using semantics.simps(4) by metis
  then show ?case using Dis_E by auto
next
  case (Con_E1 p q a)
  then show ?case using semantics.simps(5) by metis
next
  case (Con_E2 p q a)
  then show ?case using semantics.simps(5) by metis
next
  case (Exi_I t p a)
  then have "semantics e f g (sub 0 t p)" by auto
  then have "semantics (\<lambda>n. if n = 0 then semantics_term e f t else e (n - 1)) f g p"
    using subst_lemma2 by blast
  then have "(? x. semantics (% n. if n = 0 then x else e (n - 1)) f g p)" by auto
  then show ?case by auto
next
  case (Uni_E p a t)
  then have "semantics e f g (Uni p)" by auto
  then have "!x. semantics (% n. if n = 0 then x else e (n - 1)) f g p" by auto
  then have "semantics (% n. if n = 0 then semantics_term e f t else e (n - 1)) f g p" by auto
  then show ?case using subst_lemma2 by blast
next
  case (Exi_E p a q c)
  let ?upd = "%e x.(% n. if n = 0 then x else e (n - 1))"
  from Exi_E have "semantics e f g (Exi p)" by auto
  then have "(? z. semantics (?upd e z) f g p)" by simp
  then obtain z where z_def: "semantics (?upd e z) f g p" by auto
  let ?f' = "f(c := \<lambda>x. z)"
  from z_def have "semantics  (e\<langle>0:z\<rangle>) f g p" using generalize_upd[of z] by simp
  then have "semantics (e\<langle>0:z\<rangle>) ?f' g p" using Exi_E(3) upd_lemma[of c p]
    by (metis Exi_E.hyps(5) news.simps(2))
  then have "semantics (e\<langle>0:semantics_term e ?f' (Fun c [])\<rangle>)?f' g p" using fun_upd_same by auto
  then have p_holds: "semantics e ?f' g (sub 0 (Fun c []) p)" using subst_lemma by blast
  from Exi_E(6) have a_holds: "list_all (semantics e ?f' g) a"
    using Exi_E(3) list_upd_lemma[of c a] by (metis Exi_E.hyps(5) news.simps(2))
  from Exi_E(5) have "semantics e ?f' g q" using p_holds a_holds
    by (metis Exi_E.hyps(4) list_all_simps(1))
  then show ?case using Exi_E(3) upd_lemma newness by (metis Exi_E.hyps(5))
next
  case (Uni_I c p a)
  let ?upd = "%e x.(% n. if n = 0 then x else e (n - 1))"
  have "(! x. semantics (?upd e x) f g p)"
    proof
      fix x
      let ?f' = "f(c := \<lambda>y. x)"
      from Uni_I have "list_all (semantics e ?f' g) a" using list_upd_lemma newness by blast
      then have "semantics e ?f' g (sub 0 (Fun c []) p)" using Uni_I by auto
      then have "semantics (?upd e (semantics_term e ?f' (Fun c []))) ?f' g p"
        using subst_lemma2 by blast
      then have "semantics (?upd e (?f' c (semantics_list e ?f' []))) ?f' g p"
        by (metis semantics_term.simps(2))
      then have "semantics (?upd e (?f' c [])) ?f' g p" by (metis fun_upd_same)
      then have "semantics (?upd e x) ?f' g p" using fun_upd_apply by metis
      then show "semantics (?upd e x) f g p" using Uni_I upd_lemma newness by blast
    qed
  then show ?case by auto
qed auto

theorem soundness: "OK p [] ==> semantics e f g p"
proof -
  have "OK p [] \<Longrightarrow> list_all (semantics e f g) [] \<Longrightarrow> semantics e f g p" using soundness' by blast
  then show "OK p [] \<Longrightarrow> semantics e f g p" by auto
qed

corollary "OK p [] \<longrightarrow> (\<forall>e f g. semantics e f g p)"
by (auto, rule soundness)

end

